/*
	MIT License http://www.opensource.org/licenses/mit-license.php
	Author Haijie Xie @hai-x
*/

"use strict";

const { Field, Flag, NODE_FIELDS, NodeType, Part } = require("./data");
const { A } = require("./syntax-parser");

// cspell:ignore defun, fnames, funarg

/**
 * @typedef {"global" | "module" | "function" | "function-expression-name" | "block" | "switch" | "catch" | "with" | "for" | "class" | "class-field-initializer" | "class-static-block"} ScopeType
 */

/**
 * Each node type's name, by its number.
 * @type {string[]}
 */
const TYPE_NAMES = [];
for (const name of Object.keys(NODE_FIELDS)) {
	TYPE_NAMES[NodeType[/** @type {keyof NodeType} */ (name)]] = name;
}

/** One occurrence of a name in the source, which a rename rewrites in place. */
class ScopeIdentifier {
	/**
	 * @param {string} name the name, escapes resolved
	 * @param {number} start where it starts in the source
	 * @param {number} end where it ends
	 */
	constructor(name, start, end) {
		/** @type {string} */
		this.name = name;
		/** @type {number} */
		this.start = start;
		/** @type {number} */
		this.end = end;
	}

	/**
	 * Where it sits in the source, as the ESTree identifier it replaces held it.
	 * @deprecated read `start` and `end`
	 * @returns {[number, number]} its start and end
	 */
	get range() {
		// TODO in the next major release: remove, `start` and `end` replace it
		return [this.start, this.end];
	}
}

/**
 * A lexical scope. One shape for every kind, so the property loads in the
 * resolution loop stay monomorphic.
 */
class Scope {
	/**
	 * @param {ScopeType} type what opened this scope
	 * @param {string} blockType the type of the node that opened it
	 * @param {number} blockStart where that node starts
	 * @param {Scope | null} upper the enclosing scope
	 * @param {boolean} isVarScope whether `var` and function declarations hoist to here
	 * @param {boolean} recordEveryReference whether every binding collects its references, not only the ones webpack reads
	 */
	constructor(
		type,
		blockType,
		blockStart,
		upper,
		isVarScope,
		recordEveryReference
	) {
		/** @type {ScopeType} */
		this.type = type;
		/** @type {string} the type of the node that opened this scope */
		this.blockType = blockType;
		/** @type {number} where that node starts */
		this.blockStart = blockStart;
		/** @type {Scope | null} */
		this.upper = upper;
		/** @type {Scope[]} */
		this.childScopes = NO_CHILD_SCOPES;
		/** @type {Variable[]} */
		this.variables = NO_VARIABLE_LIST;
		/** @type {Map<string, Variable> | undefined} the index, once this scope outgrows a scan */
		this._index = undefined;
		/** @type {Scope} the nearest enclosing scope `var` hoists to */
		this.variableScope = isVarScope
			? this
			: /** @type {Scope} */ (upper).variableScope;
		/**
		 * For a function scope with parameters, the offset where its body
		 * starts; `-1` for every other scope. Separates the two regions that
		 * share this scope, so a reference in the parameter list can be kept
		 * from resolving to a binding declared in the body — see
		 * `isHiddenBodyBinding`.
		 * @type {number}
		 */
		this.paramBoundary = -1;
		/**
		 * Whether this scope's bindings collect their references — only the
		 * module scope and its direct children are ever asked. See `_resolve`.
		 * @type {boolean}
		 */
		this._recorded =
			recordEveryReference ||
			type === "module" ||
			(upper !== null && upper.type === "module");
		if (upper !== null) {
			if (upper.childScopes === NO_CHILD_SCOPES) upper.childScopes = [this];
			else upper.childScopes.push(this);
		}
	}

	/**
	 * @param {string} name name to look up
	 * @returns {Variable | undefined} the binding this scope declares under that name
	 */
	getBinding(name) {
		const index = this._index;
		if (index !== undefined) return index.get(name);
		const variables = this.variables;
		for (let i = 0; i < variables.length; i++) {
			const variable = variables[i];
			if (variable.name === name) return variable;
		}
		return undefined;
	}
}

/** A binding: one name declared in one scope. */
class Variable {
	/**
	 * @param {string} name the declared name
	 * @param {Scope} scope the declaring scope
	 */
	constructor(name, scope) {
		/** @type {string} */
		this.name = name;
		/** @type {ScopeIdentifier[]} declaring occurrences */
		this.identifiers = NO_IDENTIFIERS;
		/** @type {Reference[]} occurrences that resolved here, at any depth */
		this.references = NO_REFERENCES;
		/** @type {Scope} */
		this.scope = scope;
	}
}

/** One identifier occurrence that refers to a binding. */
class Reference {
	/**
	 * @param {ScopeIdentifier} identifier the occurrence
	 * @param {Scope} from the scope the identifier was seen in
	 */
	constructor(identifier, from) {
		/** @type {ScopeIdentifier} */
		this.identifier = identifier;
		/** @type {Scope} */
		this.from = from;
		/** @type {Variable | undefined} set during resolution, absent when free */
		this.resolved = undefined;
	}
}

/**
 * Stand-ins for the collections of a scope that declares nothing and encloses
 * nothing — over half of them are one or both. Each is replaced by a real
 * collection when the scope first needs it. None of them is ever mutated.
 * @type {Variable[]}
 */
const NO_VARIABLE_LIST = [];
/** @type {Scope[]} */
const NO_CHILD_SCOPES = [];
/** @type {Reference[]} */
const NO_REFERENCES = [];
/** @type {ScopeIdentifier[]} */
const NO_IDENTIFIERS = [];

/**
 * Above this many bindings a scope indexes them in a `Map`; below it, scanning
 * the list is as fast and costs no second structure. ~96% of the scopes that
 * bind anything stay below.
 */
const INDEX_THRESHOLD = 8;

/**
 * Adds a binding to a scope, seeding its list on the first one and building an
 * index once the scope has outgrown a scan.
 * @param {Scope} scope the scope that just declared a name
 * @param {Variable} variable the binding it declared
 * @returns {void}
 */
const addBinding = (scope, variable) => {
	const variables = scope.variables;
	if (variables === NO_VARIABLE_LIST) {
		scope.variables = [variable];
		return;
	}
	variables.push(variable);
	const index = scope._index;
	if (index !== undefined) {
		index.set(variable.name, variable);
		return;
	}
	if (variables.length <= INDEX_THRESHOLD) return;
	/** @type {Map<string, Variable>} */
	const built = new Map();
	for (let i = 0; i < variables.length; i++) {
		built.set(variables[i].name, variables[i]);
	}
	scope._index = built;
};

/**
 * Statement types that provably declare nothing in the block that holds them —
 * `var` hoists past it, and the rest bind nowhere. Anything else, a syntax
 * this list has not heard of included, is assumed to declare.
 */
const STATEMENTS_WITHOUT_BINDINGS = new Uint8Array(TYPE_NAMES.length);
for (const type of [
	NodeType.BlockStatement,
	NodeType.BreakStatement,
	NodeType.ContinueStatement,
	NodeType.DebuggerStatement,
	NodeType.DoWhileStatement,
	NodeType.EmptyStatement,
	NodeType.ExpressionStatement,
	NodeType.ForInStatement,
	NodeType.ForOfStatement,
	NodeType.ForStatement,
	NodeType.IfStatement,
	NodeType.ReturnStatement,
	NodeType.SwitchStatement,
	NodeType.ThrowStatement,
	NodeType.TryStatement,
	NodeType.WhileStatement,
	NodeType.WithStatement
]) {
	STATEMENTS_WITHOUT_BINDINGS[type] = 1;
}

/**
 * Whether a binding found in a function scope is invisible to a reference,
 * because the reference sits in the parameter list and the binding is declared
 * in the body.
 *
 * Parameters and body share one scope here, but the language gives them two:
 * a function with parameters evaluates them first, and only then creates the
 * environment its body declarations live in. So a parameter default reads the
 * enclosing scope, never the body.
 *
 * A name declared in *both* places is not hidden — that is what keeps the `x`
 * in `function f(x) { var x = 1; return x }` resolving to the parameter.
 * @param {Variable} variable a binding found in a function scope with parameters
 * @param {number} start where the identifier being resolved starts
 * @param {number} boundary source offset where that function's body starts
 * @returns {boolean} true when resolution must skip this binding and climb
 * @example
 * ```js
 * const x = 1;
 * function f(a = x) { const x = 2; }
 * // the default reads the outer `x`; the body's `x` does not exist yet
 * ```
 */
const isHiddenBodyBinding = (variable, start, boundary) => {
	// a reference in the body sees everything the scope holds
	if (start >= boundary) return false;
	const identifiers = variable.identifiers;
	for (let i = 0; i < identifiers.length; i++) {
		// declared in the parameter list too, so the parameters do see it
		if (identifiers[i].start < boundary) return false;
	}
	return true;
};

// WHY: the analysis reads the tree's columns itself, not through `A`: it runs
// with the optimizing compiler off in the benchmarks, where every read through
// the path is a call, and it reads every node once.
const LAYOUT = A._tree;
const FIELD_SLOTS = LAYOUT._fieldSlots;
const FIELD_STRIDE = LAYOUT._fieldStride;
const PART_SLOTS = LAYOUT._partSlots;
const PART_STRIDE = LAYOUT._partStride;
const IDENTIFIER_NAME = LAYOUT._nameSlots[NodeType.Identifier];

/**
 * Where a node of a type keeps a field in its record: the field's slot, or `-1`
 * where the type has no such field.
 * @param {number} type a `NodeType`
 * @param {number} field a `Field`
 * @returns {number} the slot, a list's included
 */
const slotOf = (type, field) => {
	const encoded = FIELD_SLOTS[type * FIELD_STRIDE + field];
	return encoded === -1 ? -1 : encoded >> 1;
};

/**
 * Each type's slot for a field, `-1` where it has none.
 * @param {number} field a `Field`
 * @returns {Int8Array} the slots by `NodeType`
 */
const slotsOf = (field) => {
	const slots = new Int8Array(TYPE_NAMES.length);
	for (let type = 0; type < TYPE_NAMES.length; type++) {
		slots[type] = slotOf(type, field);
	}
	return slots;
};

const ID_SLOT = slotsOf(Field.id);
const PARAMS_SLOT = slotsOf(Field.params);
const BODY_SLOT = slotsOf(Field.body);
const KEY_SLOT = slotsOf(Field.key);
const VALUE_SLOT = slotsOf(Field.value);
const LEFT_SLOT = slotsOf(Field.left);
const LOCAL_SLOT = slotsOf(Field.local);
const LABEL_SLOT = slotsOf(Field.label);
const ARGUMENT_SLOT = slotsOf(Field.argument);
const PROPERTIES_SLOT = slotsOf(Field.properties);
const ELEMENTS_SLOT = slotsOf(Field.elements);
const MEMBER_PROPERTY = slotOf(NodeType.MemberExpression, Field.property);
const META_META = slotOf(NodeType.MetaProperty, Field.meta);
const META_PROPERTY = slotOf(NodeType.MetaProperty, Field.property);
const IMPORTED = slotOf(NodeType.ImportSpecifier, Field.imported);
const EXPORTED = slotsOf(Field.exported);
const EXPORT_SOURCE = slotOf(NodeType.ExportNamedDeclaration, Field.source);
const EXPORT_SPECIFIERS = slotOf(
	NodeType.ExportNamedDeclaration,
	Field.specifiers
);
const ATTRIBUTE_KEY = slotOf(NodeType.ImportAttribute, Field.key);
const DECLARATIONS = slotOf(NodeType.VariableDeclaration, Field.declarations);
const DECLARATOR_ID = slotOf(NodeType.VariableDeclarator, Field.id);
const DECLARATOR_INIT = slotOf(NodeType.VariableDeclarator, Field.init);
const DECLARATION_KIND =
	PART_SLOTS[NodeType.VariableDeclaration * PART_STRIDE + Part.kind];
const ASSIGNMENT_OPERATOR =
	PART_SLOTS[NodeType.AssignmentExpression * PART_STRIDE + Part.operator];
const FOR_INIT = slotOf(NodeType.ForStatement, Field.init);
const CATCH_PARAM = slotOf(NodeType.CatchClause, Field.param);
const WITH_BODY = slotOf(NodeType.WithStatement, Field.body);
const SWITCH_DISCRIMINANT = slotOf(
	NodeType.SwitchStatement,
	Field.discriminant
);
const SWITCH_CASES = slotOf(NodeType.SwitchStatement, Field.cases);
const CASE_CONSEQUENT = slotOf(NodeType.SwitchCase, Field.consequent);
const BLOCK_BODY = slotOf(NodeType.BlockStatement, Field.body);

/**
 * What the pass does at each node type, so its dispatch is one table read and
 * a `switch` over small integers; `0` for the types it passes over.
 */
const ACTION = new Uint8Array(TYPE_NAMES.length);
const IDENTIFIER = 1;
const MEMBER = 2;
const PROPERTY = 3;
const METHOD = 4;
const FIELD = 5;
const LABELLED = 6;
const META = 7;
const FUNCTION_DECLARATION = 8;
const FUNCTION_EXPRESSION = 9;
const ARROW = 10;
const CLASS_DECLARATION = 11;
const CLASS_EXPRESSION = 12;
const DECLARATION = 13;
const FOR = 14;
const FOR_IN = 15;
const CATCH = 16;
const WITH = 17;
const BLOCK = 18;
const SWITCH = 19;
const STATIC_BLOCK = 20;
const ASSIGNMENT = 21;
const IMPORT_SPECIFIER = 22;
const IMPORT_LOCAL = 23;
const EXPORT_SPECIFIER = 24;
const EXPORT_NAMED = 25;
const EXPORT_ALL = 26;
const ATTRIBUTE = 27;
ACTION[NodeType.Identifier] = IDENTIFIER;
ACTION[NodeType.MemberExpression] = MEMBER;
ACTION[NodeType.Property] = PROPERTY;
ACTION[NodeType.MethodDefinition] = METHOD;
ACTION[NodeType.PropertyDefinition] = FIELD;
ACTION[NodeType.LabeledStatement] = LABELLED;
ACTION[NodeType.BreakStatement] = LABELLED;
ACTION[NodeType.ContinueStatement] = LABELLED;
ACTION[NodeType.MetaProperty] = META;
ACTION[NodeType.FunctionDeclaration] = FUNCTION_DECLARATION;
ACTION[NodeType.FunctionExpression] = FUNCTION_EXPRESSION;
ACTION[NodeType.ArrowFunctionExpression] = ARROW;
ACTION[NodeType.ClassDeclaration] = CLASS_DECLARATION;
ACTION[NodeType.ClassExpression] = CLASS_EXPRESSION;
ACTION[NodeType.VariableDeclaration] = DECLARATION;
ACTION[NodeType.ForStatement] = FOR;
ACTION[NodeType.ForInStatement] = FOR_IN;
ACTION[NodeType.ForOfStatement] = FOR_IN;
ACTION[NodeType.CatchClause] = CATCH;
ACTION[NodeType.WithStatement] = WITH;
ACTION[NodeType.BlockStatement] = BLOCK;
ACTION[NodeType.SwitchStatement] = SWITCH;
ACTION[NodeType.StaticBlock] = STATIC_BLOCK;
ACTION[NodeType.AssignmentExpression] = ASSIGNMENT;
ACTION[NodeType.ImportSpecifier] = IMPORT_SPECIFIER;
ACTION[NodeType.ImportDefaultSpecifier] = IMPORT_LOCAL;
ACTION[NodeType.ImportNamespaceSpecifier] = IMPORT_LOCAL;
ACTION[NodeType.ExportSpecifier] = EXPORT_SPECIFIER;
ACTION[NodeType.ExportNamedDeclaration] = EXPORT_NAMED;
ACTION[NodeType.ExportAllDeclaration] = EXPORT_ALL;
ACTION[NodeType.ImportAttribute] = ATTRIBUTE;

/** Where a declaring identifier binds, relative to the scope it sits in. */
const BINDS_HERE = 1;
const BINDS_VAR = 2;
// a class declaration's name: in the class scope and the one around it
const BINDS_HERE_AND_ABOVE = 3;

/** How a pattern's names bind, as a declaration or an assignment reads them. */
const DEFINE = 0;
const DEFINE_INIT = 1;
const ASSIGN = 2;

/**
 * One scope as the pass finds it: the source interval its names sit in.
 * `analyzeScope` nests them and turns each into a `Scope` once the whole tree
 * is read.
 */
class ScopeRecord {
	/**
	 * @param {ScopeType} type what opens it
	 * @param {number} block the node that opens it
	 * @param {number} from where the names it holds start in the source
	 * @param {number} to where they end
	 * @param {boolean} isVarScope whether `var` hoists to it
	 */
	constructor(type, block, from, to, isVarScope) {
		/** @type {ScopeType} */
		this.type = type;
		/** @type {number} */
		this.block = block;
		/** @type {number} */
		this.from = from;
		/** @type {number} */
		this.to = to;
		/** @type {boolean} */
		this.isVarScope = isVarScope;
		/** @type {number} where a function's body starts, `-1` without parameters */
		this.paramBoundary = -1;
		/** @type {boolean} whether it binds `arguments` */
		this.hasArguments = false;
		/** @type {boolean} whether it is a function's body block, which the function's scope is */
		this.folded = false;
		/** @type {Scope | null} */
		this.scope = null;
	}
}

// the node types and flags the reader tests, read once
const ARRAY_EXPRESSION_TYPE = NodeType.ArrayExpression;
const ARRAY_PATTERN_TYPE = NodeType.ArrayPattern;
const ARROW_FUNCTION_EXPRESSION_TYPE = NodeType.ArrowFunctionExpression;
const ASSIGNMENT_EXPRESSION_TYPE = NodeType.AssignmentExpression;
const ASSIGNMENT_PATTERN_TYPE = NodeType.AssignmentPattern;
const IDENTIFIER_TYPE = NodeType.Identifier;
const MEMBER_EXPRESSION_TYPE = NodeType.MemberExpression;
const OBJECT_EXPRESSION_TYPE = NodeType.ObjectExpression;
const OBJECT_PATTERN_TYPE = NodeType.ObjectPattern;
const PROPERTY_TYPE = NodeType.Property;
const REST_ELEMENT_TYPE = NodeType.RestElement;
const SPREAD_ELEMENT_TYPE = NodeType.SpreadElement;
const SWITCH_CASE_TYPE = NodeType.SwitchCase;
const VARIABLE_DECLARATION_TYPE = NodeType.VariableDeclaration;
const COMPUTED_FLAG = Flag.computed;
const SHORTHAND_FLAG = Flag.shorthand;
const ASYNC_FLAG = Flag.async;

/**
 * Reads a tree once, in node order, for the scopes and names of the
 * concatenation analysis. A parse writes children before their parent, so
 * each node meets its children already read: an identifier is a read until the
 * node holding it says otherwise.
 */
class ScopeReader {
	/**
	 * @param {SyntaxTree} tree the tree
	 * @param {number} program its program, the last node a parse writes
	 */
	constructor(tree, program) {
		/** @type {SyntaxTree} */
		this.tree = tree;
		const size = program + 1;
		/** @type {Uint8Array} how many reads each identifier makes */
		this.reads = new Uint8Array(size);
		/** @type {Uint8Array} where each declaring identifier binds, `0` for none */
		this.binds = new Uint8Array(size);
		/** @type {Int32Array} every identifier, in node order */
		this.identifiers = new Int32Array(size);
		/** @type {number} how many `identifiers` holds */
		this.identifierCount = 0;
		/** @type {ScopeRecord[]} every scope but the module's and the global one */
		this.records = [];
		/** @type {Map<number, ScopeRecord>} the scope of each block that opens one */
		this.blockRecords = new Map();
		/** @type {Set<number>} where each shorthand property's identifier starts */
		this.shorthandIdentifierStarts = new Set();
	}

	/**
	 * Records a scope over the names from `from` to the end of `block`.
	 * @param {ScopeType} type what opens it
	 * @param {number} block the node that opens it
	 * @param {number} from where the names it holds start
	 * @param {boolean} isVarScope whether `var` hoists to it
	 * @returns {ScopeRecord} the scope
	 */
	_scope(type, block, from, isVarScope) {
		const record = new ScopeRecord(
			type,
			block,
			from,
			this.tree._ends[block],
			isVarScope
		);
		this.records.push(record);
		return record;
	}

	/**
	 * Gives a pattern's names their binding and reads, as `_bind` of a walk did:
	 * each default a name sits under reads it once more.
	 * @param {number} node the pattern, `0` for a hole
	 * @param {number} mode `DEFINE`, `DEFINE_INIT` or `ASSIGN`
	 * @param {number} binds where its names bind
	 * @param {number} defaults how many defaults hold it
	 * @returns {void}
	 */
	_pattern(node, mode, binds, defaults) {
		if (node === 0) return;
		const tree = this.tree;
		const type = tree._types[node];
		const base = tree._bases[node];
		const slots = tree._slots;
		switch (type) {
			case IDENTIFIER_TYPE:
				if (mode !== ASSIGN) this.binds[node] = binds;
				this.reads[node] = mode === DEFINE ? defaults : defaults + 1;
				return;
			case OBJECT_PATTERN_TYPE:
			case OBJECT_EXPRESSION_TYPE:
				this._patternList(
					slots[base + PROPERTIES_SLOT[type]],
					mode,
					binds,
					defaults
				);
				return;
			case ARRAY_PATTERN_TYPE:
			case ARRAY_EXPRESSION_TYPE:
				this._patternList(
					slots[base + ELEMENTS_SLOT[type]],
					mode,
					binds,
					defaults
				);
				return;
			case PROPERTY_TYPE:
				this._pattern(slots[base + VALUE_SLOT[type]], mode, binds, defaults);
				return;
			case ASSIGNMENT_PATTERN_TYPE:
			case ASSIGNMENT_EXPRESSION_TYPE:
				this._pattern(slots[base + LEFT_SLOT[type]], mode, binds, defaults + 1);
				return;
			case REST_ELEMENT_TYPE:
			case SPREAD_ELEMENT_TYPE:
				this._pattern(slots[base + ARGUMENT_SLOT[type]], mode, binds, defaults);
		}
	}

	/**
	 * @param {number} list a tree list of patterns
	 * @param {number} mode `DEFINE`, `DEFINE_INIT` or `ASSIGN`
	 * @param {number} binds where its names bind
	 * @param {number} defaults how many defaults hold it
	 * @returns {void}
	 */
	_patternList(list, mode, binds, defaults) {
		const tree = this.tree;
		const first = tree._listStarts[list];
		const count = tree._listLengths[list];
		const items = tree._listItems;
		for (let i = 0; i < count; i++) {
			this._pattern(items[first + i], mode, binds, defaults);
		}
	}

	/**
	 * Counts one more read of each name a pattern declares, as a loop head
	 * writes them on every iteration.
	 * @param {number} node the pattern, `0` for a hole
	 * @returns {void}
	 */
	_readDeclared(node) {
		if (node === 0) return;
		const tree = this.tree;
		const type = tree._types[node];
		const base = tree._bases[node];
		const slots = tree._slots;
		switch (type) {
			case IDENTIFIER_TYPE:
				this.reads[node]++;
				return;
			case OBJECT_PATTERN_TYPE:
			case ARRAY_PATTERN_TYPE: {
				const list =
					slots[
						base +
							(type === OBJECT_PATTERN_TYPE
								? PROPERTIES_SLOT[type]
								: ELEMENTS_SLOT[type])
					];
				const first = tree._listStarts[list];
				const count = tree._listLengths[list];
				for (let i = 0; i < count; i++) {
					this._readDeclared(tree._listItems[first + i]);
				}
				return;
			}
			case PROPERTY_TYPE:
				this._readDeclared(slots[base + VALUE_SLOT[type]]);
				return;
			case ASSIGNMENT_PATTERN_TYPE:
				this._readDeclared(slots[base + LEFT_SLOT[type]]);
				return;
			case REST_ELEMENT_TYPE:
				this._readDeclared(slots[base + ARGUMENT_SLOT[type]]);
		}
	}

	/**
	 * Whether a statement list declares something a scope of its own has to hold.
	 * @param {number} list a tree list of statements
	 * @returns {boolean} true when a scope has to be opened for it
	 */
	_needsScope(list) {
		const tree = this.tree;
		const types = tree._types;
		const first = tree._listStarts[list];
		const count = tree._listLengths[list];
		for (let i = 0; i < count; i++) {
			const statement = tree._listItems[first + i];
			if (statement === 0) continue;
			const type = types[statement];
			if (type === VARIABLE_DECLARATION_TYPE) {
				if (!this._isVar(statement)) return true;
			} else if (type === SWITCH_CASE_TYPE) {
				const consequent =
					tree._slots[tree._bases[statement] + CASE_CONSEQUENT];
				if (this._needsScope(consequent)) return true;
			} else if (STATEMENTS_WITHOUT_BINDINGS[type] !== 1) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @param {number} declaration a variable declaration
	 * @returns {boolean} whether it declares with `var`
	 */
	_isVar(declaration) {
		const tree = this.tree;
		const value = tree._slots[tree._bases[declaration] + DECLARATION_KIND];
		return tree._values[value - 1] === "var";
	}

	/**
	 * Records a function's scope, which its body block's scope is.
	 * @param {number} node the function
	 * @param {number} type its type
	 * @param {number} id its name, `0` for none, which binds outside this scope
	 * @returns {void}
	 */
	_function(node, type, id) {
		const tree = this.tree;
		const base = tree._bases[node];
		const slots = tree._slots;
		const params = slots[base + PARAMS_SLOT[type]];
		const body = slots[base + BODY_SLOT[type]];
		this._patternList(params, DEFINE, BINDS_HERE, 0);
		const record = this._scope(
			"function",
			node,
			id !== 0 ? tree._ends[id] : tree._starts[node],
			true
		);
		if (type !== ARROW_FUNCTION_EXPRESSION_TYPE) record.hasArguments = true;
		if (tree._listLengths[params] !== 0) {
			record.paramBoundary = tree._starts[body];
		}
		const folded = this.blockRecords.get(body);
		if (folded !== undefined) folded.folded = true;
	}

	/**
	 * Reads every node up to the program.
	 * @param {number} program the program
	 * @returns {void}
	 */
	read(program) {
		const tree = this.tree;
		const types = tree._types;
		const starts = tree._starts;
		const ends = tree._ends;
		const flags = tree._flags;
		const bases = tree._bases;
		const slots = tree._slots;
		const reads = this.reads;
		const binds = this.binds;
		const identifiers = this.identifiers;
		let identifierCount = 0;
		for (let node = 1; node < program; node++) {
			const type = types[node];
			const action = ACTION[type];
			if (action === 0) continue;
			if (
				action >= FUNCTION_DECLARATION &&
				action <= ARROW &&
				(flags[node] & ASYNC_FLAG) !== 0
			) {
				// the parser reads `async` as a name before it knows a function
				// follows, then drops it; that name is where the function starts
				const start = starts[node];
				for (let i = identifierCount - 1; i >= 0; i--) {
					const at = starts[identifiers[i]];
					if (at < start) break;
					if (at === start) reads[identifiers[i]] = 0;
				}
			}
			const base = bases[node];
			switch (action) {
				case IDENTIFIER:
					reads[node] = 1;
					identifiers[identifierCount++] = node;
					break;
				case MEMBER:
					if ((flags[node] & COMPUTED_FLAG) === 0) {
						reads[slots[base + MEMBER_PROPERTY]] = 0;
					}
					break;
				case PROPERTY: {
					const value = slots[base + VALUE_SLOT[type]];
					if ((flags[node] & SHORTHAND_FLAG) !== 0) {
						this.shorthandIdentifierStarts.add(
							starts[
								types[value] === ASSIGNMENT_PATTERN_TYPE
									? slots[bases[value] + LEFT_SLOT[ASSIGNMENT_PATTERN_TYPE]]
									: value
							]
						);
					}
					if ((flags[node] & COMPUTED_FLAG) === 0) {
						reads[slots[base + KEY_SLOT[type]]] = 0;
					}
					break;
				}
				case METHOD:
					if ((flags[node] & COMPUTED_FLAG) === 0) {
						reads[slots[base + KEY_SLOT[type]]] = 0;
					}
					break;
				case FIELD: {
					if ((flags[node] & COMPUTED_FLAG) === 0) {
						reads[slots[base + KEY_SLOT[type]]] = 0;
					}
					const value = slots[base + VALUE_SLOT[type]];
					if (value !== 0) {
						// each field initializer runs in its own scope
						this._scope("class-field-initializer", value, starts[value], true);
					}
					break;
				}
				case LABELLED:
					reads[slots[base + LABEL_SLOT[type]]] = 0;
					break;
				case META:
					reads[slots[base + META_META]] = 0;
					reads[slots[base + META_PROPERTY]] = 0;
					break;
				case FUNCTION_DECLARATION: {
					// block scoped in ES6, so it binds in the scope around
					const id = slots[base + ID_SLOT[type]];
					if (id !== 0) {
						binds[id] = BINDS_HERE;
						reads[id] = 0;
					}
					this._function(node, type, id);
					break;
				}
				case FUNCTION_EXPRESSION: {
					const id = slots[base + ID_SLOT[type]];
					if (id === 0) {
						this._function(node, type, 0);
						break;
					}
					// a named function expression gets a scope above its own
					// holding only its name
					binds[id] = BINDS_HERE;
					reads[id] = 0;
					this._function(node, type, id);
					this._scope("function-expression-name", node, starts[node], false);
					break;
				}
				case ARROW:
					this._function(node, type, 0);
					break;
				case CLASS_DECLARATION:
				case CLASS_EXPRESSION: {
					// bound outside, so siblings see the class, and inside, so the
					// body sees a binding an outer reassignment cannot change
					const id = slots[base + ID_SLOT[type]];
					if (id !== 0 && types[id] === IDENTIFIER_TYPE) {
						binds[id] =
							action === CLASS_DECLARATION ? BINDS_HERE_AND_ABOVE : BINDS_HERE;
						reads[id] = 0;
					}
					this._scope("class", node, starts[node], false);
					break;
				}
				case DECLARATION: {
					const where = this._isVar(node) ? BINDS_VAR : BINDS_HERE;
					const list = slots[base + DECLARATIONS];
					const first = tree._listStarts[list];
					const count = tree._listLengths[list];
					for (let i = 0; i < count; i++) {
						const declarator = tree._listItems[first + i];
						const declaratorBase = bases[declarator];
						this._pattern(
							slots[declaratorBase + DECLARATOR_ID],
							slots[declaratorBase + DECLARATOR_INIT] !== 0
								? DEFINE_INIT
								: DEFINE,
							where,
							0
						);
					}
					break;
				}
				case FOR: {
					const init = slots[base + FOR_INIT];
					if (
						init !== 0 &&
						types[init] === VARIABLE_DECLARATION_TYPE &&
						!this._isVar(init)
					) {
						this._scope("for", node, starts[node], false);
					}
					break;
				}
				case FOR_IN: {
					const left = slots[base + LEFT_SLOT[type]];
					if (types[left] !== VARIABLE_DECLARATION_TYPE) {
						this._pattern(left, ASSIGN, 0, 0);
						break;
					}
					// the loop head writes each name it declares on every iteration
					const list = slots[bases[left] + DECLARATIONS];
					const first = tree._listStarts[list];
					const count = tree._listLengths[list];
					for (let i = 0; i < count; i++) {
						this._readDeclared(
							slots[bases[tree._listItems[first + i]] + DECLARATOR_ID]
						);
					}
					if (!this._isVar(left)) {
						this._scope("for", node, starts[node], false);
					}
					break;
				}
				case CATCH:
					this._pattern(slots[base + CATCH_PARAM], DEFINE, BINDS_HERE, 0);
					this._scope("catch", node, starts[node], false);
					break;
				case WITH:
					// the object is read outside the scope the body runs in
					this._scope("with", node, starts[slots[base + WITH_BODY]], false);
					break;
				case BLOCK:
					if (this._needsScope(slots[base + BLOCK_BODY])) {
						this.blockRecords.set(
							node,
							this._scope("block", node, starts[node], false)
						);
					}
					break;
				case SWITCH:
					if (this._needsScope(slots[base + SWITCH_CASES])) {
						this._scope(
							"switch",
							node,
							ends[slots[base + SWITCH_DISCRIMINANT]],
							false
						);
					}
					break;
				case STATIC_BLOCK:
					this._scope("class-static-block", node, starts[node], true);
					break;
				case ASSIGNMENT: {
					const left = slots[base + LEFT_SLOT[type]];
					const leftType = types[left];
					if (
						leftType !== IDENTIFIER_TYPE &&
						leftType !== MEMBER_EXPRESSION_TYPE &&
						tree._values[slots[base + ASSIGNMENT_OPERATOR] - 1] === "="
					) {
						this._pattern(left, ASSIGN, 0, 0);
					}
					break;
				}
				case IMPORT_SPECIFIER:
					reads[slots[base + IMPORTED]] = 0;
				// falls through
				case IMPORT_LOCAL: {
					const local = slots[base + LOCAL_SLOT[type]];
					binds[local] = BINDS_HERE;
					reads[local] = 0;
					break;
				}
				case EXPORT_SPECIFIER:
					// `export { x }` reads `x`; the exported name is not a binding
					reads[slots[base + EXPORTED[type]]] = 0;
					break;
				case EXPORT_NAMED:
					if (slots[base + EXPORT_SOURCE] !== 0) {
						// a re-export reads nothing of this module
						const list = slots[base + EXPORT_SPECIFIERS];
						const first = tree._listStarts[list];
						const count = tree._listLengths[list];
						for (let i = 0; i < count; i++) {
							const specifier = tree._listItems[first + i];
							reads[slots[bases[specifier] + LOCAL_SLOT[types[specifier]]]] = 0;
						}
					}
					break;
				case EXPORT_ALL:
					reads[slots[base + EXPORTED[type]]] = 0;
					break;
				case ATTRIBUTE:
					reads[slots[base + ATTRIBUTE_KEY]] = 0;
					break;
			}
		}
		this.identifierCount = identifierCount;
	}
}

/**
 * Makes the `Scope` of a scope the pass found, inside the one around it.
 * @param {ScopeRecord} record the scope found
 * @param {Scope} upper the scope around it
 * @param {boolean} recordEveryReference whether every binding collects its references
 * @returns {Scope} the scope
 */
const openScope = (record, upper, recordEveryReference) => {
	const scope = new Scope(
		record.type,
		TYPE_NAMES[A.type(record.block)],
		A.start(record.block),
		upper,
		record.isVarScope,
		recordEveryReference
	);
	record.scope = scope;
	scope.paramBoundary = record.paramBoundary;
	if (record.hasArguments) {
		// every non-arrow function has an implicit `arguments`
		addBinding(scope, new Variable("arguments", scope));
	}
	return scope;
};

/**
 * Orders scopes by where their names start, a scope before the ones inside
 * it; of two over the same interval the one found later holds the other.
 * @param {ScopeRecord} a a scope
 * @param {ScopeRecord} b another
 * @returns {number} their order
 */
const compareRecords = (a, b) => a.from - b.from || b.to - a.to;

/**
 * Puts the identifiers that read or declare in source order. A parse writes
 * most in it already, so each is appended, and one written late, as a class's
 * name after its body, is put in place by a binary search and one native move.
 * @param {Int32Array} identifiers identifiers in node order
 * @param {number} count how many it holds
 * @param {Int32Array} starts where each node starts
 * @param {Uint8Array} reads how many reads each identifier makes
 * @param {Uint8Array} binds where each declaring identifier binds
 * @returns {Int32Array} those identifiers in source order, `0` after the last
 */
const sortByStart = (identifiers, count, starts, reads, binds) => {
	const order = new Int32Array(count + 1);
	let length = 0;
	let last = -1;
	for (let i = 0; i < count; i++) {
		const identifier = identifiers[i];
		if (reads[identifier] === 0 && binds[identifier] === 0) continue;
		const start = starts[identifier];
		if (start >= last) {
			order[length++] = identifier;
			last = start;
			continue;
		}
		let low = 0;
		let high = length;
		while (low < high) {
			const middle = (low + high) >> 1;
			if (starts[order[middle]] <= start) low = middle + 1;
			else high = middle;
		}
		order.copyWithin(low + 1, low, length);
		order[low] = identifier;
		length++;
	}
	return order;
};

/**
 * Declares a name in a scope, reusing the binding when it already exists
 * (`var x; var x;`, a function and its hoisted declaration, and so on).
 * @param {Scope} scope scope to declare in
 * @param {ScopeIdentifier} occurrence the declaring occurrence
 * @returns {void}
 */
const define = (scope, occurrence) => {
	const name = occurrence.name;
	let variable = scope.getBinding(name);
	if (variable === undefined) {
		variable = new Variable(name, scope);
		addBinding(scope, variable);
	}
	if (variable.identifiers === NO_IDENTIFIERS) {
		variable.identifiers = [occurrence];
	} else {
		variable.identifiers.push(occurrence);
	}
};

/**
 * Stacks a scope's bindings on their names, as the sweep enters it.
 * @param {Map<string, Variable[]>} visible the bindings of the open scopes, by name
 * @param {Scope} scope the scope entered
 * @returns {void}
 */
const enterScope = (visible, scope) => {
	const variables = scope.variables;
	for (let i = 0; i < variables.length; i++) {
		const variable = variables[i];
		const bindings = visible.get(variable.name);
		if (bindings === undefined) visible.set(variable.name, [variable]);
		else bindings.push(variable);
	}
};

/**
 * Takes a scope's bindings off their names, as the sweep leaves it.
 * @param {Map<string, Variable[]>} visible the bindings of the open scopes, by name
 * @param {Scope} scope the scope left
 * @returns {void}
 */
const leaveScope = (visible, scope) => {
	const variables = scope.variables;
	for (let i = 0; i < variables.length; i++) {
		/** @type {Variable[]} */ (visible.get(variables[i].name)).pop();
	}
};

/**
 * @typedef {object} ScopeAnalysis
 * @property {Scope} globalScope the outermost scope
 * @property {Scope} moduleScope the module body scope, where top-level declarations live
 * @property {Reference[]} unresolvedReferences every identifier that resolved to no binding — the module's free names
 * @property {Set<number>} shorthandIdentifierStarts where each shorthand property's identifier starts, so a rename can write `name: newName` without the tree
 */

/**
 * Analyses a generated module source as a strict ES module, reading the tree
 * `A` reads. Only the module scope and its direct children collect references;
 * `recordEveryReference` widens that to the whole tree, retaining one per identifier.
 * @param {number} program the program to analyse
 * @param {boolean=} recordEveryReference whether every binding collects its references
 * @returns {ScopeAnalysis} the scope tree and the module's free references
 */
const analyzeScope = (program, recordEveryReference = false) => {
	const tree = A._tree;
	const reader = new ScopeReader(tree, program);
	reader.read(program);
	const starts = tree._starts;
	const ends = tree._ends;
	const globalScope = new Scope(
		"global",
		"Program",
		starts[program],
		null,
		true,
		recordEveryReference
	);
	const moduleScope = new Scope(
		"module",
		"Program",
		starts[program],
		globalScope,
		true,
		recordEveryReference
	);
	/** @type {ScopeRecord[]} */
	const records = [];
	const found = reader.records;
	// found inner first: reversed, the stable sort keeps an outer one first
	for (let i = found.length - 1; i >= 0; i--) {
		if (!found[i].folded) records.push(found[i]);
	}
	records.sort(compareRecords);

	const { identifiers, identifierCount, reads, binds } = reader;
	const values = tree._values;
	const slots = tree._slots;
	const bases = tree._bases;
	const order = sortByStart(identifiers, identifierCount, starts, reads, binds);

	// declare every name first, in source order, as a `var` an inner block
	// declares lands among its function's own
	/** @type {ScopeIdentifier[]} */
	const occurrences = [];
	/** @type {Int32Array} where each declaring identifier's occurrence is in `occurrences`, from 1 */
	const occurrenceOf = new Int32Array(order.length);
	/** @type {ScopeRecord[]} the scopes holding the current position, innermost last */
	const open = [];
	let scope = moduleScope;
	let to = Infinity;
	let next = 0;
	let nextFrom = records.length > 0 ? records[0].from : Infinity;
	for (let i = 0; ; i++) {
		const node = order[i];
		if (node === 0) break;
		const where = binds[node];
		if (where === 0) continue;
		const start = starts[node];
		if (start >= to || start >= nextFrom) {
			// scopes open in source order, so each is made inside the one around it
			while (start >= nextFrom) {
				const record = records[next++];
				nextFrom = next < records.length ? records[next].from : Infinity;
				while (open.length > 0 && open[open.length - 1].to < record.to) {
					open.pop();
				}
				openScope(
					record,
					open.length > 0
						? /** @type {Scope} */ (open[open.length - 1].scope)
						: moduleScope,
					recordEveryReference
				);
				open.push(record);
			}
			while (open.length > 0 && open[open.length - 1].to <= start) open.pop();
			const top = open.length > 0 ? open[open.length - 1] : null;
			scope = top !== null ? /** @type {Scope} */ (top.scope) : moduleScope;
			to = top !== null ? top.to : Infinity;
		}
		// one occurrence however many scopes it binds in or reads from, so a
		// rename meets it once
		const occurrence = new ScopeIdentifier(
			/** @type {string} */ (values[slots[bases[node] + IDENTIFIER_NAME] - 1]),
			start,
			ends[node]
		);
		occurrenceOf[i] = occurrences.push(occurrence);
		if (where === BINDS_VAR) {
			define(scope.variableScope, occurrence);
		} else if (where === BINDS_HERE_AND_ABOVE) {
			define(/** @type {Scope} */ (scope.upper), occurrence);
			define(scope, occurrence);
		} else {
			define(scope, occurrence);
		}
	}
	while (next < records.length) {
		const record = records[next++];
		while (open.length > 0 && open[open.length - 1].to < record.to) open.pop();
		openScope(
			record,
			open.length > 0
				? /** @type {Scope} */ (open[open.length - 1].scope)
				: moduleScope,
			recordEveryReference
		);
		open.push(record);
	}

	// then resolve every read in source order: entering a scope stacks its
	// bindings on their names, so a read finds the innermost on its name's stack
	/** @type {Map<string, Variable[]>} the bindings of the open scopes, by name, innermost last */
	const visible = new Map();
	enterScope(visible, moduleScope);
	/** @type {Reference[]} */
	const unresolved = [];
	open.length = 0;
	scope = moduleScope;
	to = Infinity;
	next = 0;
	nextFrom = records.length > 0 ? records[0].from : Infinity;
	for (let i = 0; ; i++) {
		const node = order[i];
		if (node === 0) break;
		const count = reads[node];
		if (count === 0) continue;
		const start = starts[node];
		if (start >= to || start >= nextFrom) {
			while (start >= nextFrom) {
				const record = records[next++];
				nextFrom = next < records.length ? records[next].from : Infinity;
				while (open.length > 0 && open[open.length - 1].to < record.to) {
					leaveScope(
						visible,
						/** @type {Scope} */ (/** @type {ScopeRecord} */ (open.pop()).scope)
					);
				}
				enterScope(visible, /** @type {Scope} */ (record.scope));
				open.push(record);
			}
			while (open.length > 0 && open[open.length - 1].to <= start) {
				leaveScope(
					visible,
					/** @type {Scope} */ (/** @type {ScopeRecord} */ (open.pop()).scope)
				);
			}
			const top = open.length > 0 ? open[open.length - 1] : null;
			scope = top !== null ? /** @type {Scope} */ (top.scope) : moduleScope;
			to = top !== null ? top.to : Infinity;
		}
		const slot = occurrenceOf[i];
		/** @type {ScopeIdentifier | undefined} */
		let occurrence = slot !== 0 ? occurrences[slot - 1] : undefined;
		const name =
			occurrence !== undefined
				? occurrence.name
				: /** @type {string} */ (
						values[slots[bases[node] + IDENTIFIER_NAME] - 1]
					);
		const bindings = visible.get(name);
		/** @type {Variable | undefined} */
		let variable;
		if (bindings !== undefined) {
			for (let j = bindings.length - 1; j >= 0; j--) {
				const binding = bindings[j];
				const boundary = binding.scope.paramBoundary;
				// `-1` is every scope but a function scope with parameters, so the
				// common case is one integer compare and no call
				if (boundary === -1 || !isHiddenBodyBinding(binding, start, boundary)) {
					variable = binding;
					break;
				}
			}
		}
		// most reads resolve into a scope nothing reads back, so the
		// `Reference` and its occurrence are made only where one is kept
		if (variable !== undefined && !variable.scope._recorded) continue;
		if (occurrence === undefined) {
			occurrence = new ScopeIdentifier(name, start, ends[node]);
		}
		for (let read = 0; read < count; read++) {
			const reference = new Reference(occurrence, scope);
			if (variable === undefined) {
				unresolved.push(reference);
				continue;
			}
			reference.resolved = variable;
			if (variable.references === NO_REFERENCES) {
				variable.references = [reference];
			} else {
				variable.references.push(reference);
			}
		}
	}

	return {
		globalScope,
		moduleScope,
		unresolvedReferences: unresolved,
		shorthandIdentifierStarts: reader.shorthandIdentifierStarts
	};
};

/** @typedef {{ name: string, definition: TreeDefinition }} NamedIdentifier a name as the mangler reads it: as written, and its definition */

// How a minifier definition's name was declared, one code per kind of
// terser's declaring symbol; a global is a name nothing declares.
const DECLARES_VAR = 1;
const DECLARES_FUNARG = 2;
const DECLARES_LET = 3;
const DECLARES_CONST = 4;
const DECLARES_USING = 5;
const DECLARES_CATCH = 6;
const DECLARES_IMPORT = 7;

// What a name one long saves taking the name spelled beside it: a key's `:`
// and the name, or an import's or export's ` as ` and the name.
const SHORTHAND_SAVING = 2;
const AS_SAVING = 5;
// `spelledNames` collecting the names a key spells too, not only a module's.
const SPELLED_KEYS = 2;
// A name the mangler may hand out as it is spelled: one ASCII identifier, so it
// prints bare and costs a byte a character.
const SPELLABLE_NAME = /^[A-Za-z_$][\w$]*$/;
// Names no binding may take in strict code, a module's, beyond the keywords.
const NAMES_NO_BINDING_TAKES = new Set([
	"arguments",
	"await",
	"enum",
	"eval",
	"implements",
	"interface",
	"let",
	"package",
	"private",
	"protected",
	"public",
	"static",
	"yield"
]);
const DECLARES_DEFUN = 8;
const DECLARES_LAMBDA = 9;
const DECLARES_CLASS = 10;
const DECLARES_DEF_CLASS = 11;
const DECLARES_GLOBAL = 12;

// What the minifier's analysis records of a name read, replayed once all is
// declared.
const REFERENCE_CALLED = 1;
const REFERENCE_EXPORTED = 1 << 1;
const REFERENCE_FROM_MODULE = 1 << 2;
const REFERENCE_CATCH = 1 << 3;
// The name is written: assigned, updated or a loop's or pattern's target.
const REFERENCE_WRITTEN = 1 << 4;
// The name is a shorthand property's value, which spells its key too.
const REFERENCE_SHORTHAND = 1 << 5;
// The name is what a call calls, not a `new` or a tag.
const REFERENCE_CALLEE = 1 << 6;
// The name is what a call passing nothing calls.
const REFERENCE_CALLED_BARE = 1 << 7;

// How an `export` naming a definition keeps its name.
const EXPORT_KEEP_NAME = 1;
const EXPORT_WANT_MANGLE = 2;

// Past this many definitions a scope's `enclosed` is also held as a set, so
// adding one stops scanning the list: a bundle's toplevel reaches thousands.
const ENCLOSED_INDEX_THRESHOLD = 16;
/** @type {WeakMap<MinifierVariable[], Set<MinifierVariable>>} */
const enclosedIndexes = new WeakMap();

/**
 * Adds a definition to a scope's `enclosed` unless it is there. The list is
 * the record, since a cloned scope copies it; the set only answers membership.
 * @param {MinifierScope} scope a scope
 * @param {MinifierVariable} definition a definition it reaches
 * @returns {void}
 */
const encloseUnique = (scope, definition) => {
	const { enclosed } = scope;
	if (enclosed.length < ENCLOSED_INDEX_THRESHOLD) {
		if (!enclosed.includes(definition)) enclosed.push(definition);
		return;
	}
	let index = enclosedIndexes.get(enclosed);
	if (index === undefined || index.size !== enclosed.length) {
		index = new Set(enclosed);
		enclosedIndexes.set(enclosed, index);
	}
	if (index.has(definition)) return;
	index.add(definition);
	enclosed.push(definition);
};

/**
 * A scope as the minifier reads it: terser's, which opens one for every block
 * and loop, besides what it names in.
 */
class MinifierScope extends Scope {
	/**
	 * @param {ScopeType} type what opened this scope
	 * @param {number} node the node opening it
	 * @param {MinifierScope | null} upper the enclosing scope
	 * @param {boolean} isVarScope whether `var` and function declarations hoist to here
	 */
	constructor(type, node, upper, isVarScope) {
		super(type, "", -1, upper, isVarScope, false);
		/** @type {number} */
		this.node = node;
		/** @type {MinifierVariable[]} the definitions it or a scope inside it reads, in the order first read */
		this.enclosed = [];
		/** @type {number} how many names it has handed out, less one */
		this.cname = -1;
		/** @type {boolean} whether a direct `eval` can reach its names */
		this.usesEval = false;
		/** @type {boolean} whether a `with` can reach its names */
		this.usesWith = false;
		/** @type {Set<string> | null} the names a `with` body inside spells, null where unknown */
		this.withNames = null;
		/** @type {MinifierVariable | null} a function expression's own name */
		this.functionName = null;
		/** @type {number} the first name its parameter list reads, as the analysis counts them, or -1 */
		this.parameterStart = -1;
		/** @type {number} the name after the last its parameter list reads, or -1 */
		this.parameterEnd = -1;
	}

	/**
	 * terser's `pinned`.
	 * @returns {boolean} whether `eval` or `with` can reach its names
	 */
	isPinned() {
		return this.usesEval || this.usesWith;
	}
}

/**
 * One name declared in one scope, or a global: terser's `SymbolDef`, less
 * what only terser's compressor reads.
 */
class MinifierVariable extends Variable {
	/**
	 * @param {string} name the declared name
	 * @param {MinifierScope} scope the declaring scope, the toplevel for a global
	 * @param {number} kind how it was first declared, as a `DECLARES_*` code
	 */
	constructor(name, scope, kind) {
		super(name, scope);
		/** @type {number} how it was first declared, as a `DECLARES_*` code */
		this.kind = kind;
		/** @type {number} every way it was declared, one bit per `DECLARES_*` code */
		this.declarations = 1 << kind;
		/** @type {boolean} whether the toplevel declares it */
		this.global = false;
		/** @type {boolean} whether nothing declares it */
		this.undeclared = false;
		/** @type {number} how an `export` naming it keeps its name, as `EXPORT_*` */
		this.export = 0;
		/** @type {string | null} the name mangling gives it */
		this.mangledName = null;
		/** @type {number} how many names read or write it, which the mangler gives the short names by */
		this.referenceCount = 0;
		/** @type {boolean} whether a name writes it, which a `SyntaxTree`'s analysis alone records */
		this.written = false;
		/** @type {number} how many names and declarations after the first write it */
		this.writes = 0;
	}
}

/**
 * Whether a definition is a variable rather than a label or another definition.
 * @param {MinifierVariable | MinifierLabel | import("./syntax-printer").NamedDefinition | null | undefined} value a definition
 * @returns {value is MinifierVariable} true when the value is a variable
 */
const isMinifierVariable = (value) => value instanceof MinifierVariable;

/** A label: a statement's, its `break`s and `continue`s naming it too. */
class MinifierLabel {
	/**
	 * @param {string} name the name
	 * @param {MinifierLabel | null} parent the label of the nearest labeled statement around, across functions
	 */
	constructor(name, parent) {
		/** @type {string} */
		this.name = name;
		/** @type {string | null} the name mangling gives it */
		this.mangledName = null;
		/** @type {MinifierLabel | null} */
		this.parent = parent;
		/** @type {number} where the mangler's label names stood when it named this one */
		this.counter = -1;
	}
}

/**
 * The options the minifier's analysis reads, its mangle options among them.
 * @typedef {object} MinifierScopeOptions
 * @property {boolean=} module whether the program is a module, so strict
 * @property {boolean=} ie8 whether catch parameters belong to their function
 * @property {boolean=} safari10 whether a loop's scope reads its parent's names, and catch parameters belong to their function
 * @property {boolean | RegExp=} keepFnames which function names survive, collecting the declarators naming one
 * @property {boolean | RegExp=} keepClassnames which class names survive, collecting the declarators naming one under `classDeclarators`
 * @property {boolean=} classDeclarators whether, under `keepClassnames`, the names declarators give anonymous classes are kept as `keepFnames` keeps a function's
 * @property {boolean=} parameterScopes whether names are scoped as the spec scopes them where terser does not: a parameter list's or a catch parameter's reads skip what the body declares, and a block's async or generator function stays in the block
 * @property {boolean=} withNames whether a scope a `with` reaches keeps only the names its body spells, mangling the rest
 * @property {number=} spelledNames which names to collect that the mangler may give the name beside them to write less: 1 for an import's or export's, 2 for a key's too
 * @property {boolean=} substitutesAliases whether each read of a `let`, `const` or body's `var` set to a name nothing writes reads that name instead, as the one pass prints it
 * @property {boolean=} movesFunctions under `substitutesAliases`, false to leave each function read once where it is declared, as terser's `inline` turned off does
 * @property {boolean=} movesToplevel whether a top-level function moves too, where the compressor drops top-level names
 */

/**
 * @typedef {object} MinifierScopeAnalysis
 * @property {MinifierScope} toplevel the program's scope, its `childScopes` in the order the mangler walks them
 * @property {MinifierLabel[]} labels every label, in the same order
 * @property {Map<string, MinifierVariable>} globals the names nothing declares, in the order first read
 * @property {Set<MinifierScope>} blockDefunScopes the function scopes holding a function declared in a block
 * @property {NamedIdentifier[] | null} functionDeclarators under `keepFnames`, the names declarators give anonymous functions, in the order the mangler asks `keepFnames` of them
 * @property {NamedIdentifier[] | null} classDeclarators under `classDeclarators` and `keepClassnames`, the names declarators give anonymous classes
 * @property {NamedIdentifier[]} catchParameters unless `ie8` or `safari10` move them, the catch parameters, each named where the mangler's walk meets its scope
 * @property {boolean} namesPrivate whether the program names a private member, which renaming walks it for
 * @property {SpelledNames | null} spelledNames under `spelledNames`, the names a key or an import or export spells for a name beside it
 * @property {(number[] | null)=} aliases under `substitutesAliases`, the declarators whose name no read reads any more
 * @property {(number[] | null)=} movedFunctions under `substitutesAliases`, each declarator of a function read once and that read, in pairs: the read prints the function
 */

/**
 * Where a name stands beside one spelled for it: a property's key, which the
 * name as its value lets print alone, or an import's or export's other name.
 * @typedef {object} SpelledNames
 * @property {NamedIdentifier[]} identifiers each name, its `definition` read once the analysis resolves
 * @property {string[]} spellings the name spelled beside each
 * @property {number[]} savings the characters each saves, its own name one long, where it takes the name spelled
 */

/**
 * @param {MinifierScope} scope the scope declaring it
 * @param {MinifierVariable} variable a definition
 * @param {number} read the read's place in the analysis's count
 * @returns {boolean} whether the read sits in the scope's parameter list and the definition in its body, which the list cannot see
 */
const isHiddenFromParameters = (scope, variable, read) =>
	read < scope.parameterEnd &&
	read >= scope.parameterStart &&
	variable.kind !== DECLARES_FUNARG &&
	variable.kind !== DECLARES_LAMBDA &&
	variable.kind !== DECLARES_CATCH;

/**
 * @param {MinifierScope} from the scope a name is read in
 * @param {string} name the name
 * @param {number=} read the read's place in the analysis's count, under `parameterScopes`
 * @returns {MinifierVariable | undefined} what it resolves to from there
 */
const findMinifierVariable = (from, name, read = -1) => {
	for (let scope = /** @type {Scope | null} */ (from); scope !== null;) {
		// `getBinding`, inlined: the interpreter pays a call per scope climbed
		const index = scope._index;
		/** @type {MinifierVariable | undefined} */
		let variable;
		if (index !== undefined) {
			variable = /** @type {MinifierVariable | undefined} */ (index.get(name));
		} else {
			const variables = scope.variables;
			for (let i = 0; i < variables.length; i++) {
				if (variables[i].name === name) {
					variable = /** @type {MinifierVariable} */ (variables[i]);
					break;
				}
			}
		}
		if (
			variable !== undefined &&
			!isHiddenFromParameters(
				/** @type {MinifierScope} */ (scope),
				variable,
				read
			)
		) {
			return variable;
		}
		scope = scope.upper;
	}
	return undefined;
};

// By `NodeType`, 1 for what lists statements, which run in their order.
/** @type {Uint8Array | undefined} */
let listsStatements;

/**
 * @param {number[]} loops each loop's start and end, in pairs
 * @param {number} from where a declaration starts
 * @param {number} start where a read after it starts
 * @param {number} end where that read ends
 * @returns {boolean} whether a loop holds the read but not the declaration
 */
const entersLoop = (loops, from, start, end) => {
	for (let i = 0; i < loops.length; i += 2) {
		if (loops[i] > from && loops[i] <= start && loops[i + 1] >= end) {
			return true;
		}
	}
	return false;
};

/**
 * @param {number[]} nodes the names read
 * @returns {number[]} their indexes, ordered by where each starts
 */
const referencesByStart = (nodes) =>
	nodes
		.map((node, i) => i)
		.sort((a, b) => A.start(nodes[a]) - A.start(nodes[b]));

/**
 * @param {number[]} byStart the indexes of the names read, ordered by start
 * @param {number[]} nodes the names read
 * @param {number} start a position
 * @returns {number} where in the order the first name starting there or after is
 */
const firstFrom = (byStart, nodes, start) => {
	let low = 0;
	let high = byStart.length;
	while (low < high) {
		const middle = (low + high) >>> 1;
		if (A.start(nodes[byStart[middle]]) < start) low = middle + 1;
		else high = middle;
	}
	return low;
};

/**
 * @param {MinifierScope} outer a scope
 * @param {MinifierScope} inner another
 * @returns {boolean} whether the first is the second or holds it
 */
const encloses = (outer, inner) => {
	for (let scope = /** @type {Scope | null} */ (inner); scope !== null;) {
		if (scope === outer) return true;
		scope = scope.upper;
	}
	return false;
};

/**
 * @param {MinifierScope} from the scope a read is in
 * @param {MinifierVariable} variable a definition in a scope holding it
 * @returns {boolean} whether a scope between declares the definition's name, which a catch parameter then takes the mangled name of
 */
const shadowedFrom = (from, variable) => {
	for (
		let scope = /** @type {Scope | null} */ (from);
		scope !== null && scope !== variable.scope;
		scope = scope.upper
	) {
		if (scope.getBinding(variable.name) !== undefined) return true;
	}
	return false;
};

/**
 * terser's `mark_enclosed`: each scope from one out to a definition's reads it.
 * @param {MinifierScope} from the scope reading it
 * @param {MinifierVariable} variable the definition
 * @returns {void}
 */
const encloseVariable = (from, variable) => {
	for (let scope = /** @type {Scope | null} */ (from); scope !== null;) {
		encloseUnique(/** @type {MinifierScope} */ (scope), variable);
		if (scope === variable.scope) break;
		scope = scope.upper;
	}
};

/**
 * Marks each scope from one out as reached by a `with`, which keeps the names
 * its body spells as written; a scope reached already keeps what it knew.
 * @param {MinifierScope} from the scope the `with` is in
 * @param {boolean} collects whether the names are collected, else all are kept
 * @returns {void}
 */
const reachByWith = (from, collects) => {
	for (
		let scope = /** @type {MinifierScope | null} */ (from);
		scope !== null;
	) {
		if (!scope.usesWith) {
			scope.usesWith = true;
			scope.withNames = collects ? new Set() : null;
		}
		scope = /** @type {MinifierScope | null} */ (scope.upper);
	}
};

/**
 * Adds the names a `with` body spells to each scope from one out.
 * @param {MinifierScope} from the scope the `with` is in
 * @param {Set<string>} names the names its body spells
 * @returns {void}
 */
const keepWithNames = (from, names) => {
	for (
		let scope = /** @type {MinifierScope | null} */ (from);
		scope !== null;
	) {
		const kept = scope.withNames;
		if (kept !== null) for (const name of names) kept.add(name);
		scope = /** @type {MinifierScope | null} */ (scope.upper);
	}
};

/**
 * @typedef {import("./syntax-parser").SyntaxTree} SyntaxTree
 * @typedef {MinifierVariable | MinifierLabel | null} TreeDefinition
 */

/**
 * The scopes the minifier's analysis reads off a `SyntaxTree`: each name's
 * definition is held by its node's number.
 * @typedef {MinifierScopeAnalysis & { definitions: TreeDefinition[] }} MinifierTreeScopeAnalysis
 */

/**
 * `MinifierScopeAnalyzer` over a `SyntaxTree` of the source terser's tree
 * was read from: the same walk, pushing the same nodes, so the same scopes,
 * definitions and orders. Under `ie8` or `safari10` catch parameters move to
 * their function in the walk's order, not the order terser walks a call in.
 */
class MinifierTreeScopeAnalyzer {
	/**
	 * @param {number} program the program, in the tree `A` reads
	 * @param {Uint8Array} types each node's type, as terser's tree types it
	 * @param {MinifierScopeOptions} options the mangle options
	 * @param {(node: number, message: string) => never} raise throws the parse error a misplaced import or export is
	 */
	constructor(program, types, options, raise) {
		/** @type {Uint8Array} */
		this.types = types;
		/** @type {(node: number, message: string) => never} */
		this.raise = raise;
		/** @type {boolean} */
		this.parameterScopes = Boolean(options.parameterScopes);
		/** @type {MinifierScope[]} */
		this.parameterRanges = [];
		/** @type {MinifierScope} */
		this.toplevel = new MinifierScope("global", program, null, true);
		/** @type {MinifierScope} */
		this.scope = this.toplevel;
		/** @type {MinifierLabel[]} */
		this.labels = [];
		/** @type {Map<string, MinifierVariable>} */
		this.globals = new Map();
		/** @type {Set<MinifierScope>} */
		this.blockDefunScopes = new Set();
		/** @type {number[] | null} */
		this.functionDeclarators = options.keepFnames ? [] : null;
		/** @type {number[] | null} */
		this.classDeclarators =
			options.classDeclarators && options.keepClassnames ? [] : null;
		/** @type {number[] | null} the `let`, `const` and body's `var` declarators set to a name */
		this.aliasDeclarators = options.substitutesAliases ? [] : null;
		/** @type {number[] | null} each declarator set to a function, and the start and end of the statements listing it */
		this.functionBindings = options.substitutesAliases ? [] : null;
		/** @type {number[] | null} each loop's start and end, in pairs */
		this.loopRanges = options.substitutesAliases ? [] : null;
		/** @type {number[] | null} where each `this` and `arguments` read starts */
		this.thisStarts = options.substitutesAliases ? [] : null;
		/** @type {boolean} whether a top-level function moves to its one read too */
		this.movesToplevel = Boolean(options.movesToplevel);
		/** @type {number[]} */
		this.referenceNodes = [];
		/** @type {MinifierScope[]} */
		this.referenceScopes = [];
		/** @type {number[]} */
		this.referenceFlags = [];
		/** @type {number[]} */
		this.catchParameters = [];
		/** @type {boolean} */
		this.legacyCatch = Boolean(options.ie8 || options.safari10);
		/** @type {boolean} */
		this.safari10 = Boolean(options.safari10);
		/** @type {number[]} under `ie8` or `safari10`, the catch parameters in the walk's order */
		this.catchNames = [];
		/** @type {MinifierScope[]} the scope of each */
		this.catchScopes = [];
		/** @type {Map<MinifierVariable, { nodes: number[], scopes: MinifierScope[] }> | null} under `ie8` or `safari10`, the names resolved to each catch parameter, and the scope reading each */
		this.catchReads = this.legacyCatch ? new Map() : null;
		/** @type {MinifierScope[]} under `safari10`, the scopes of `for` loops */
		this.forScopes = [];
		/** @type {boolean} */
		this.namesPrivate = false;
		/** @type {number[]} the nodes terser's walk has pushed, 0 for an arrow's implicit `return` */
		this.stack = [];
		/** @type {boolean} */
		this.strict = Boolean(options.module);
		/** @type {Map<string, MinifierLabel>} */
		this.labelsInScope = new Map();
		/** @type {MinifierLabel | null} */
		this.currentLabel = null;
		/** @type {number} the pattern the walk is inside, 0 for none */
		this.inDestructuring = 0;
		/** @type {Set<string> | null} the names the `with` body visited spells, while one is */
		this.namesInWith = null;
		/** @type {boolean} whether the names a `with` body spells are collected, to mangle the rest */
		this.collectsWithNames = Boolean(options.withNames);
		/** @type {boolean} whether the name visited is an assignment's or a loop's target */
		this.assigning = false;
		// Filled in place: `Array.from` takes four times as long on a large tree.
		/** @type {TreeDefinition[]} */
		this.definitions = /** @type {TreeDefinition[]} */ (
			// eslint-disable-next-line unicorn/no-new-array
			new Array(types.length)
		).fill(null);
		/** @type {number[] | null} each name with one spelled beside it */
		this.spelledIdentifiers = options.spelledNames ? [] : null;
		/** @type {string[]} the name spelled beside each */
		this.spellings = [];
		/** @type {number[]} the characters each pair saves */
		this.spelledSavings = [];
		/** @type {boolean} whether a key spells a name, which prints alone where it is its value's */
		this.spelledKeys = options.spelledNames === SPELLED_KEYS;
	}

	/**
	 * Collects a name and one spelled beside it, under `spelledNames`.
	 * @param {number} identifier the name, 0 for none
	 * @param {number} spelled what spells the other, 0 for none
	 * @param {number} saving the characters it saves taking that name
	 * @returns {void}
	 */
	_spell(identifier, spelled, saving) {
		const identifiers = this.spelledIdentifiers;
		const { types } = this;
		if (
			identifiers === null ||
			identifier === 0 ||
			spelled === 0 ||
			types[identifier] !== NodeType.Identifier
		) {
			return;
		}
		/** @type {ReturnType<SyntaxTree["value"]>} */
		let spelling;
		if (types[spelled] === NodeType.Identifier) {
			spelling = A.name(spelled);
		} else if (types[spelled] === NodeType.Literal) {
			spelling = A.value(spelled);
		}
		if (
			typeof spelling !== "string" ||
			!SPELLABLE_NAME.test(spelling) ||
			NAMES_NO_BINDING_TAKES.has(spelling) ||
			// A shorthand `__proto__` is an own property; `__proto__:` sets the prototype.
			spelling === "__proto__"
		) {
			return;
		}
		identifiers.push(identifier);
		this.spellings.push(spelling);
		this.spelledSavings.push(saving);
	}

	/**
	 * Collects a property's value named as its key could be, under `spelledNames`.
	 * @param {number} property a property of an object or a pattern
	 * @returns {void}
	 */
	_spellProperty(property) {
		if (!this.spelledKeys || A.flag(Flag.computed, property)) {
			return;
		}
		const value = A.field(0, Field.value, property);
		this._spell(
			this.types[value] === NodeType.AssignmentPattern
				? A.field(0, Field.left, value)
				: value,
			A.field(0, Field.key, property),
			SHORTHAND_SAVING
		);
	}

	/**
	 * @returns {SpelledNames | null} the names collected under `spelledNames`, resolved
	 */
	_spelledNames() {
		const identifiers = this.spelledIdentifiers;
		if (identifiers === null) return null;
		return {
			identifiers: this._asNames(identifiers),
			spellings: this.spellings,
			savings: this.spelledSavings
		};
	}

	/**
	 * @param {number} field the `Field`
	 * @param {number} node a node
	 * @param {number=} i the item's index, for a list
	 * @returns {number} the node the field holds, past parentheses, 0 for none
	 */
	_child(field, node, i = 0) {
		let child = A.field(i, field, node);
		while (child !== 0 && A.type(child) === NodeType.ParenthesizedExpression) {
			child = A.field(0, Field.expression, child);
		}
		return child;
	}

	/**
	 * @param {number} field the `Field`, a list
	 * @param {number} node a node
	 * @returns {void}
	 */
	_visitList(field, node) {
		const count = A.fieldCount(field, node);
		for (let i = 0; i < count; i++) {
			const child = this._child(field, node, i);
			if (child !== 0) this._visit(child);
		}
	}

	/**
	 * @param {number} field the `Field`
	 * @param {number} node a node
	 * @returns {void}
	 */
	_visitChild(field, node) {
		const child = this._child(field, node);
		if (child !== 0) this._visit(child);
	}

	/**
	 * @param {number} node a node
	 * @returns {string} the name it is, a quoted module name's among them
	 */
	_nameOf(node) {
		return A.type(node) === NodeType.Literal
			? String(A.value(node))
			: A.name(node);
	}

	/**
	 * @param {ScopeType} type what opens it
	 * @param {number} node the node opening it
	 * @param {boolean} isVarScope whether `var` hoists to here
	 * @returns {MinifierScope} the scope, now current
	 */
	_open(type, node, isVarScope) {
		const scope = new MinifierScope(type, node, this.scope, isVarScope);
		this.scope = scope;
		return scope;
	}

	/**
	 * @param {ScopeType} type what opens it
	 * @param {number} node a block's node
	 * @returns {MinifierScope} the scope it leaves
	 */
	_enterBlock(type, node) {
		const outer = this.scope;
		const scope = this._open(type, node, false);
		scope.usesWith = outer.usesWith;
		scope.withNames = outer.withNames;
		return outer;
	}

	/**
	 * Visits a `with` body, collecting the names it reads, writes and declares.
	 * @param {() => void} visit visits the body
	 * @returns {void}
	 */
	_visitWithBody(visit) {
		const from = this.scope;
		reachByWith(from, this.collectsWithNames);
		if (!this.collectsWithNames) {
			visit();
			return;
		}
		const outer = this.namesInWith;
		/** @type {Set<string>} */
		const names = new Set();
		this.namesInWith = names;
		const { referenceNodes } = this;
		const first = referenceNodes.length;
		visit();
		for (let i = first; i < referenceNodes.length; i++) {
			names.add(A.name(referenceNodes[i]));
		}
		this.namesInWith = outer;
		if (outer !== null) for (const name of names) outer.add(name);
		keepWithNames(from, names);
	}

	/**
	 * terser's `def_variable`.
	 * @param {MinifierScope} target the scope declaring it
	 * @param {number} identifier the name declaring it, 0 for none written
	 * @param {string} name the name
	 * @param {number} kind how it is declared
	 * @returns {MinifierVariable} its definition, made or joined
	 */
	_defineVariable(target, identifier, name, kind) {
		if (this.namesInWith !== null) this.namesInWith.add(name);
		let variable = /** @type {MinifierVariable | undefined} */ (
			target.getBinding(name)
		);
		if (variable !== undefined) {
			variable.declarations |= 1 << kind;
			// A second declaration may set it again.
			variable.written = true;
			variable.writes++;
		} else {
			variable = new MinifierVariable(name, target, kind);
			variable.global = target.upper === null;
			addBinding(target, variable);
		}
		if (identifier !== 0) this.definitions[identifier] = variable;
		return variable;
	}

	/**
	 * @param {MinifierScope} from the scope reading it
	 * @param {MinifierVariable} variable what it reads
	 * @returns {void}
	 */
	_referenceVariable(from, variable) {
		variable.referenceCount++;
		encloseVariable(from, variable);
	}

	/**
	 * terser's `mark_export`, counting levels on the walk's stack.
	 * @param {MinifierVariable} variable a definition just made
	 * @param {number} level where its declaration's statement is
	 * @returns {void}
	 */
	_markExport(variable, level) {
		const { stack } = this;
		if (this.inDestructuring !== 0) {
			let i = 0;
			do {
				level++;
			} while (stack[stack.length - 1 - i++] !== this.inDestructuring);
		}
		const node = stack[stack.length - 1 - level];
		const type = node === undefined ? 0 : this.types[node];
		// A declaration repeating an exported name without `export` keeps it
		// exported, as the module still exports that binding.
		if (
			type !== NodeType.ExportNamedDeclaration &&
			type !== NodeType.ExportDefaultDeclaration &&
			type !== NodeType.ExportAllDeclaration
		) {
			return;
		}
		variable.export =
			type === NodeType.ExportDefaultDeclaration && !this._exportsValue(node)
				? EXPORT_WANT_MANGLE
				: EXPORT_KEEP_NAME;
	}

	/**
	 * @param {number} node an `export default`
	 * @returns {boolean} whether terser holds what it exports as a value, not a named declaration
	 */
	_exportsValue(node) {
		const declaration = A.field(0, Field.declaration, node);
		const type = A.type(declaration);
		return (
			(type !== NodeType.FunctionDeclaration &&
				type !== NodeType.ClassDeclaration) ||
			A.field(0, Field.id, declaration) === 0
		);
	}

	/**
	 * @param {number} node an import or export
	 * @param {string} type terser's name for it
	 * @returns {void}
	 */
	_checkModuleStatement(node, type) {
		if (this.scope !== this.toplevel) {
			this.raise(node, `"${type}" statement may only appear at the top level`);
		}
	}

	/**
	 * @param {number} node a name read, or a re-exported string
	 * @param {number} flags what else is known of it, as `REFERENCE_*` bits
	 * @returns {void}
	 */
	_addReference(node, flags) {
		this.referenceNodes.push(node);
		this.referenceScopes.push(this.scope);
		this.referenceFlags.push(flags);
	}

	/**
	 * A name a declaration or a pattern binds, or reads where `kind` is 0.
	 * @param {number} node the name or pattern
	 * @param {number} kind how it declares, as a `DECLARES_*` code, or 0
	 * @returns {void}
	 */
	_visitBinding(node, kind) {
		const { stack } = this;
		switch (this.types[node]) {
			case NodeType.Identifier:
				if (kind === 0) {
					this.assigning = true;
					this._visit(node);
					this.assigning = false;
				} else {
					this._declare(node, kind);
				}
				return;
			case NodeType.ObjectPattern:
				this._visitPattern(node, Field.properties, kind);
				return;
			case NodeType.ArrayPattern:
				this._visitPattern(node, Field.elements, kind);
				return;
			case NodeType.AssignmentPattern:
				stack.push(node);
				this._visitBinding(this._child(Field.left, node), kind);
				this._visit(this._child(Field.right, node));
				stack.pop();
				return;
			case NodeType.RestElement:
				stack.push(node);
				this._visitBinding(this._child(Field.argument, node), kind);
				stack.pop();
				return;
			default:
				this._visit(node);
		}
	}

	/**
	 * @param {number} pattern an object or array pattern
	 * @param {number} field its properties or elements
	 * @param {number} kind how it declares, as a `DECLARES_*` code, or 0
	 * @returns {void}
	 */
	_visitPattern(pattern, field, kind) {
		const { stack } = this;
		const outer = this.inDestructuring;
		this.inDestructuring = pattern;
		stack.push(pattern);
		const count = A.fieldCount(field, pattern);
		for (let i = 0; i < count; i++) {
			const element = this._child(field, pattern, i);
			if (element === 0) continue;
			if (this.types[element] !== NodeType.Property) {
				this._visitBinding(element, kind);
				continue;
			}
			stack.push(element);
			if (A.flag(Flag.computed, element)) {
				this._visitChild(Field.key, element);
			}
			this._visitBinding(this._child(Field.value, element), kind);
			this._spellProperty(element);
			stack.pop();
		}
		stack.pop();
		this.inDestructuring = outer;
	}

	/**
	 * A `var`, parameter, `let`, `const`, `using`, catch parameter or import.
	 * @param {number} identifier the name declared
	 * @param {number} kind how, as a `DECLARES_*` code
	 * @returns {void}
	 */
	_declare(identifier, kind) {
		const name = A.name(identifier);
		const { scope } = this;
		if (kind === DECLARES_IMPORT) {
			this._defineVariable(scope, identifier, name, kind);
			return;
		}
		const blockDeclaration =
			kind === DECLARES_LET ||
			kind === DECLARES_CONST ||
			kind === DECLARES_USING ||
			kind === DECLARES_CATCH;
		const defun = /** @type {MinifierScope} */ (scope.variableScope);
		// A redeclaration terser refuses here the tree's parser refused first.
		const variable = this._defineVariable(
			blockDeclaration ? scope : defun,
			identifier,
			name,
			kind
		);
		if (kind !== DECLARES_FUNARG) this._markExport(variable, 2);
		if (defun !== scope) {
			encloseVariable(scope, variable);
			const found = /** @type {MinifierVariable} */ (
				findMinifierVariable(scope, name)
			);
			if (found !== variable) {
				this.definitions[identifier] = found;
				this._referenceVariable(scope, found);
				this._recordCatchRead(identifier, scope, found);
			}
		}
		if (kind === DECLARES_CATCH) {
			this._addReference(identifier, REFERENCE_CATCH);
			if (this.catchReads !== null) {
				if (!this.catchReads.has(variable)) {
					this.catchReads.set(variable, { nodes: [], scopes: [] });
				}
				this.catchNames.push(identifier);
				this.catchScopes.push(scope);
			} else {
				this.catchParameters.push(identifier);
			}
		}
	}

	/**
	 * Under `ie8` or `safari10`, records a name resolved to a catch parameter,
	 * which `_moveCatchParameters` moves to the function's definition.
	 * @param {number} node the name
	 * @param {MinifierScope} from the scope reading it
	 * @param {MinifierVariable} variable what it resolved to
	 * @returns {void}
	 */
	_recordCatchRead(node, from, variable) {
		if (this.catchReads === null) return;
		const reads = this.catchReads.get(variable);
		if (reads === undefined) return;
		reads.nodes.push(node);
		reads.scopes.push(from);
	}

	/**
	 * @param {number} node a binding pattern, 0 for an array's hole
	 * @param {string} name a name
	 * @returns {boolean} whether the pattern binds the name
	 */
	_bindsName(node, name) {
		if (node === 0) return false;
		switch (this.types[node]) {
			case NodeType.ObjectPattern:
				return this._someChild(Field.properties, node, (property) =>
					this._bindsName(
						this.types[property] === NodeType.Property
							? this._child(Field.value, property)
							: property,
						name
					)
				);
			case NodeType.ArrayPattern:
				return this._someChild(Field.elements, node, (element) =>
					this._bindsName(element, name)
				);
			case NodeType.AssignmentPattern:
				return this._bindsName(this._child(Field.left, node), name);
			case NodeType.RestElement:
				return this._bindsName(this._child(Field.argument, node), name);
			default:
				return A.name(node) === name;
		}
	}

	/**
	 * @param {number} field the `Field`, a list
	 * @param {number} node a node
	 * @param {(child: number) => boolean} test what a child is asked
	 * @returns {boolean} whether it holds for a child, holes 0
	 */
	_someChild(field, node, test) {
		const count = A.fieldCount(field, node);
		for (let i = 0; i < count; i++) {
			if (test(this._child(field, node, i))) return true;
		}
		return false;
	}

	/**
	 * @param {number} node a statement, or a loop's head, 0 for none
	 * @param {string} name a name
	 * @returns {boolean} whether it declares the name with `let`, `const`, `using` or a class
	 */
	_declaresLexically(node, name) {
		if (node === 0) return false;
		const type = this.types[node];
		if (type === NodeType.VariableDeclaration) {
			return (
				A.textOf(Part.kind, node) !== "var" &&
				this._someChild(Field.declarations, node, (declarator) =>
					this._bindsName(A.field(0, Field.id, declarator), name)
				)
			);
		}
		return (
			type === NodeType.ClassDeclaration &&
			A.name(A.field(0, Field.id, node)) === name
		);
	}

	/**
	 * @param {number} owner a node listing statements
	 * @param {number} field the `Field` listing them
	 * @param {string} name a name
	 * @returns {boolean} whether one of them declares it lexically
	 */
	_listDeclaresLexically(owner, field, name) {
		const count = A.fieldCount(field, owner);
		for (let i = 0; i < count; i++) {
			if (this._declaresLexically(A.field(i, field, owner), name)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Annex B's test for a sloppy block's function: a `var` of its name would be
	 * an early error, which keeps the function in its block.
	 * @param {MinifierScope} scope the scope the function is declared in
	 * @param {string} name the function's name
	 * @returns {boolean} true for `f` in `{ let f; { function f() {} } }`
	 */
	_keepsInBlock(scope, name) {
		while (scope !== scope.variableScope) {
			const { node } = scope;
			switch (this.types[node]) {
				case NodeType.BlockStatement:
					if (this._listDeclaresLexically(node, Field.body, name)) return true;
					break;
				case NodeType.SwitchStatement: {
					const count = A.fieldCount(Field.cases, node);
					for (let i = 0; i < count; i++) {
						const branch = A.field(i, Field.cases, node);
						if (this._listDeclaresLexically(branch, Field.consequent, name)) {
							return true;
						}
					}
					break;
				}
				case NodeType.ForStatement:
					if (this._declaresLexically(this._child(Field.init, node), name)) {
						return true;
					}
					break;
				case NodeType.ForInStatement:
				case NodeType.ForOfStatement:
					if (this._declaresLexically(this._child(Field.left, node), name)) {
						return true;
					}
					break;
				case NodeType.CatchClause: {
					const param = A.field(0, Field.param, node);
					if (
						(param !== 0 &&
							this.types[param] !== NodeType.Identifier &&
							this._bindsName(param, name)) ||
						this._listDeclaresLexically(
							A.field(0, Field.body, node),
							Field.body,
							name
						)
					) {
						return true;
					}
					break;
				}
			}
			scope = /** @type {MinifierScope} */ (scope.upper);
		}
		const { node } = scope;
		if (this.types[node] === NodeType.Program) {
			return this._listDeclaresLexically(node, Field.body, name);
		}
		// A function holding a statement has a block for its body.
		return (
			this._someChild(Field.params, node, (param) =>
				this._bindsName(param, name)
			) ||
			this._listDeclaresLexically(
				this._child(Field.body, node),
				Field.body,
				name
			)
		);
	}

	/**
	 * @param {number} node a function
	 * @returns {void}
	 */
	_visitFunction(node) {
		const { stack } = this;
		const outerStrict = this.strict;
		const outer = this.scope;
		const outerLabels = this.labelsInScope;
		const type = this.types[node];
		const parentType = this.types[stack[stack.length - 1]];
		const inBlock =
			type === NodeType.FunctionDeclaration &&
			parentType !== NodeType.Program &&
			parentType !== NodeType.FunctionDeclaration &&
			parentType !== NodeType.FunctionExpression &&
			parentType !== NodeType.ArrowFunctionExpression &&
			parentType !== NodeType.StaticBlock;
		if (inBlock) {
			this.blockDefunScopes.add(
				/** @type {MinifierScope} */ (outer.variableScope)
			);
		}
		stack.push(node);
		const lambda = this._open("function", node, true);
		if (type !== NodeType.ArrowFunctionExpression) {
			this._defineVariable(lambda, 0, "arguments", DECLARES_FUNARG);
		}
		this.labelsInScope = new Map();
		const id = A.field(0, Field.id, node);
		if (id === 0) {
			// An arrow or a method has no name of its own.
		} else if (type === NodeType.FunctionDeclaration) {
			const name = A.name(id);
			this._markExport(
				this._defineVariable(
					// Annex B hoists a sloppy block's plain function only.
					this.strict ||
						(this.parameterScopes &&
							(A.flag(Flag.async, node) ||
								A.flag(Flag.generator, node) ||
								(inBlock && this._keepsInBlock(outer, name))))
						? outer
						: /** @type {MinifierScope} */ (outer.variableScope),
					id,
					name,
					DECLARES_DEFUN
				),
				1
			);
		} else {
			this._defineVariable(lambda, id, A.name(id), DECLARES_LAMBDA);
			lambda.functionName = /** @type {MinifierVariable} */ (
				this.definitions[id]
			);
		}
		const params = A.fieldCount(Field.params, node);
		const ranged = this.parameterScopes && params !== 0;
		if (ranged) {
			lambda.parameterStart = this.referenceNodes.length;
			this.parameterRanges.push(lambda);
		}
		for (let i = 0; i < params; i++) {
			this._visitBinding(this._child(Field.params, node, i), DECLARES_FUNARG);
		}
		if (ranged) lambda.parameterEnd = this.referenceNodes.length;
		const body = this._child(Field.body, node);
		if (this.types[body] === NodeType.BlockStatement) {
			this._visitList(Field.body, body);
		} else {
			// terser's arrow returns its expression from a statement of its own.
			stack.push(0);
			this._visit(body);
			stack.pop();
		}
		this.scope = outer;
		this.labelsInScope = outerLabels;
		this.strict = outerStrict;
		stack.pop();
	}

	/**
	 * @param {number} node a class
	 * @returns {void}
	 */
	_visitClass(node) {
		const outerStrict = this.strict;
		const outer = this.scope;
		const outerLabels = this.labelsInScope;
		this.stack.push(node);
		this.strict = true;
		const classScope = this._open("class", node, true);
		this.labelsInScope = new Map();
		const id = A.field(0, Field.id, node);
		if (id !== 0) {
			const name = A.name(id);
			this._markExport(
				this.types[node] === NodeType.ClassDeclaration
					? this._defineVariable(outer, id, name, DECLARES_DEF_CLASS)
					: this._defineVariable(classScope, id, name, DECLARES_CLASS),
				1
			);
		}
		this._visitChild(Field.superClass, node);
		this._visitList(Field.body, A.field(0, Field.body, node));
		this.scope = outer;
		this.labelsInScope = outerLabels;
		this.strict = outerStrict;
		this.stack.pop();
	}

	/**
	 * @param {number[]} stack the nodes being visited, a declaration last
	 * @returns {boolean} whether the declaration is a statement of a function's body or of the program
	 */
	_declaresInBody(stack) {
		// A function's body is visited as its list, so the function holds it.
		const type = this.types[stack[stack.length - 2]];
		return (
			type === NodeType.Program ||
			type === NodeType.FunctionDeclaration ||
			type === NodeType.FunctionExpression ||
			type === NodeType.ArrowFunctionExpression
		);
	}

	/**
	 * @param {number} node a `var`, `let`, `const` or `using`
	 * @returns {void}
	 */
	_visitDeclaration(node) {
		const { stack, functionDeclarators, classDeclarators } = this;
		const text = A.textOf(Part.kind, node);
		const kind =
			text === "var"
				? DECLARES_VAR
				: text === "let"
					? DECLARES_LET
					: text === "const"
						? DECLARES_CONST
						: DECLARES_USING;
		stack.push(node);
		const count = A.fieldCount(Field.declarations, node);
		for (let i = 0; i < count; i++) {
			const declarator = A.field(i, Field.declarations, node);
			const id = A.field(0, Field.id, declarator);
			const init = this._child(Field.init, declarator);
			if (
				functionDeclarators !== null &&
				kind !== DECLARES_USING &&
				this.types[id] === NodeType.Identifier &&
				init !== 0 &&
				(this.types[init] === NodeType.FunctionExpression ||
					this.types[init] === NodeType.ArrowFunctionExpression) &&
				A.field(0, Field.id, init) === 0
			) {
				functionDeclarators.push(id);
			} else if (
				classDeclarators !== null &&
				kind !== DECLARES_USING &&
				this.types[id] === NodeType.Identifier &&
				init !== 0 &&
				this.types[init] === NodeType.ClassExpression &&
				A.field(0, Field.id, init) === 0
			) {
				classDeclarators.push(id);
			}
			if (
				this.aliasDeclarators !== null &&
				(kind === DECLARES_LET ||
					kind === DECLARES_CONST ||
					// A `var` a function's body sets, run before what follows it there.
					(kind === DECLARES_VAR && this._declaresInBody(stack))) &&
				this.types[id] === NodeType.Identifier &&
				init !== 0 &&
				this.types[init] === NodeType.Identifier
			) {
				this.aliasDeclarators.push(declarator);
			} else if (
				this.functionBindings !== null &&
				kind !== DECLARES_USING &&
				/** @type {Uint8Array} */ (listsStatements)[
					this.types[stack[stack.length - 2]]
				] === 1 &&
				this.types[id] === NodeType.Identifier &&
				init !== 0 &&
				(this.types[init] === NodeType.FunctionExpression ||
					this.types[init] === NodeType.ArrowFunctionExpression)
			) {
				const list = stack[stack.length - 2];
				this.functionBindings.push(declarator, A.start(list), A.end(list));
			}
			stack.push(declarator);
			this._visitBinding(id, kind);
			if (init !== 0) this._visit(init);
			stack.pop();
		}
		stack.pop();
	}

	/**
	 * A loop's children, its scope entered.
	 * @param {number} node the loop
	 * @returns {void}
	 */
	_visitLoop(node) {
		switch (this.types[node]) {
			case NodeType.ForStatement:
				this._visitChild(Field.init, node);
				this._visitChild(Field.test, node);
				this._visitChild(Field.update, node);
				break;
			case NodeType.WhileStatement:
				this._visitChild(Field.test, node);
				break;
			case NodeType.DoWhileStatement:
				this._visitChild(Field.body, node);
				this._visitChild(Field.test, node);
				return;
			default:
				this._visitBinding(this._child(Field.left, node), 0);
				this._visitChild(Field.right, node);
		}
		this._visitChild(Field.body, node);
	}

	/**
	 * Reads one node as `MinifierScopeAnalyzer#_visitPrint` reads terser's.
	 * @param {number} node node to visit
	 * @returns {void}
	 */
	_visit(node) {
		const { stack } = this;
		const type = this.types[node];
		switch (type) {
			case NodeType.Identifier: {
				// A number too large for a double, which terser holds as an atom.
				if (A.type(node) !== NodeType.Identifier) return;
				const parent = stack[stack.length - 1];
				const parentType = this.types[parent];
				if (this.thisStarts !== null && A.name(node) === "arguments") {
					this.thisStarts.push(A.start(node));
				}
				this._addReference(
					node,
					A.name(node) === "eval" &&
						(parentType === NodeType.CallExpression ||
							parentType === NodeType.NewExpression)
						? REFERENCE_CALLED
						: this.assigning ||
							  parentType === NodeType.UpdateExpression ||
							  (parentType === NodeType.AssignmentExpression &&
									this._child(Field.left, parent) === node)
							? REFERENCE_WRITTEN
							: parentType === NodeType.Property &&
								  A.flag(Flag.shorthand, parent)
								? REFERENCE_SHORTHAND
								: parentType === NodeType.CallExpression &&
									  this._child(Field.callee, parent) === node
									? A.fieldCount(Field.arguments, parent) === 0
										? REFERENCE_CALLEE | REFERENCE_CALLED_BARE
										: REFERENCE_CALLEE
									: 0
				);
				return;
			}
			case NodeType.MemberExpression: {
				stack.push(node);
				this._visitChild(Field.object, node);
				const property = this._child(Field.property, node);
				if (A.flag(Flag.computed, node)) {
					this._visit(property);
				} else if (A.type(property) === NodeType.PrivateIdentifier) {
					this.namesPrivate = true;
				}
				stack.pop();
				return;
			}
			case NodeType.CallExpression:
			case NodeType.NewExpression:
				// terser's walk reaches the arguments first.
				stack.push(node);
				this._visitList(Field.arguments, node);
				this._visitChild(Field.callee, node);
				stack.pop();
				return;
			case NodeType.Literal:
				return;
			case NodeType.ThisExpression:
				if (this.thisStarts !== null) this.thisStarts.push(A.start(node));
				return;
			case NodeType.ExpressionStatement: {
				const directive = A.textOf(Part.directive, node);
				if (directive !== null) {
					if (directive === "use strict") this.strict = true;
					return;
				}
				stack.push(node);
				this._visitChild(Field.expression, node);
				stack.pop();
				return;
			}
			case NodeType.BinaryExpression:
			case NodeType.LogicalExpression:
			case NodeType.AssignmentExpression:
				stack.push(node);
				this._visitChild(Field.left, node);
				this._visitChild(Field.right, node);
				stack.pop();
				return;
			case NodeType.BlockStatement: {
				stack.push(node);
				const outer = this._enterBlock("block", node);
				this._visitList(Field.body, node);
				this.scope = outer;
				stack.pop();
				return;
			}
			case NodeType.ReturnStatement:
			case NodeType.UnaryExpression:
			case NodeType.UpdateExpression:
			case NodeType.ThrowStatement:
			case NodeType.AwaitExpression:
			case NodeType.SpreadElement:
			case NodeType.YieldExpression:
				stack.push(node);
				this._visitChild(Field.argument, node);
				stack.pop();
				return;
			case NodeType.VariableDeclaration:
				this._visitDeclaration(node);
				return;
			case NodeType.FunctionDeclaration:
			case NodeType.FunctionExpression:
			case NodeType.ArrowFunctionExpression: {
				const parent = stack[stack.length - 1];
				if (
					type === NodeType.FunctionDeclaration &&
					this.functionBindings !== null &&
					/** @type {Uint8Array} */ (listsStatements)[this.types[parent]] ===
						1 &&
					this.types[parent] !== NodeType.BlockStatement &&
					this.types[parent] !== NodeType.SwitchCase &&
					this.types[parent] !== NodeType.StaticBlock
				) {
					// Hoisted, it is made as its function or the program starts.
					this.functionBindings.push(node, A.start(parent), A.start(parent));
				}
				this._visitFunction(node);
				return;
			}
			case NodeType.ClassDeclaration:
			case NodeType.ClassExpression:
				this._visitClass(node);
				return;
			case NodeType.ForStatement:
			case NodeType.ForInStatement:
			case NodeType.ForOfStatement:
			case NodeType.WhileStatement:
			case NodeType.DoWhileStatement: {
				if (this.loopRanges !== null) {
					this.loopRanges.push(A.start(node), A.end(node));
				}
				stack.push(node);
				const outer = this._enterBlock(
					type === NodeType.WhileStatement || type === NodeType.DoWhileStatement
						? "block"
						: "for",
					node
				);
				if (
					this.safari10 &&
					type !== NodeType.WhileStatement &&
					type !== NodeType.DoWhileStatement
				) {
					this.forScopes.push(this.scope);
				}
				this._visitLoop(node);
				this.scope = outer;
				stack.pop();
				return;
			}
			case NodeType.SwitchStatement: {
				stack.push(node);
				const outer = this._enterBlock("switch", node);
				// The switched expression belongs to the scope around the switch.
				const block = this.scope;
				this.scope = outer;
				this._visitChild(Field.discriminant, node);
				this.scope = block;
				this._visitList(Field.cases, node);
				this.scope = outer;
				stack.pop();
				return;
			}
			case NodeType.CatchClause: {
				stack.push(node);
				const outer = this._enterBlock("catch", node);
				const catchScope = this.scope;
				const param = A.field(0, Field.param, node);
				const ranged = this.parameterScopes && param !== 0;
				if (ranged) {
					catchScope.parameterStart = this.referenceNodes.length;
					this.parameterRanges.push(catchScope);
				}
				if (param !== 0) this._visitBinding(param, DECLARES_CATCH);
				if (ranged) catchScope.parameterEnd = this.referenceNodes.length;
				this._visitList(Field.body, A.field(0, Field.body, node));
				this.scope = outer;
				stack.pop();
				return;
			}
			case NodeType.StaticBlock: {
				const outer = this.scope;
				const outerLabels = this.labelsInScope;
				stack.push(node);
				this._open("class-static-block", node, true);
				this.labelsInScope = new Map();
				this._visitList(Field.body, node);
				this.scope = outer;
				this.labelsInScope = outerLabels;
				stack.pop();
				return;
			}
			case NodeType.LabeledStatement: {
				// The tree's parser refuses a label defined twice or undefined.
				const labelName = A.field(0, Field.label, node);
				const name = A.name(labelName);
				const label = new MinifierLabel(name, this.currentLabel);
				this.labels.push(label);
				this.definitions[labelName] = label;
				this.labelsInScope.set(name, label);
				stack.push(node);
				this.currentLabel = label;
				this._visitChild(Field.body, node);
				this.currentLabel = label.parent;
				stack.pop();
				this.labelsInScope.delete(name);
				return;
			}
			case NodeType.BreakStatement:
			case NodeType.ContinueStatement: {
				const labelName = A.field(0, Field.label, node);
				if (labelName === 0) return;
				this.definitions[labelName] = /** @type {MinifierLabel} */ (
					this.labelsInScope.get(A.name(labelName))
				);
				return;
			}
			case NodeType.WithStatement:
				stack.push(node);
				this._visitChild(Field.object, node);
				this._visitWithBody(() => this._visitChild(Field.body, node));
				stack.pop();
				return;
			case NodeType.Property:
			case NodeType.PropertyDefinition:
				if (
					A.type(A.field(0, Field.key, node)) === NodeType.PrivateIdentifier
				) {
					this.namesPrivate = true;
				}
				stack.push(node);
				if (A.flag(Flag.computed, node)) this._visitChild(Field.key, node);
				this._visitChild(Field.value, node);
				if (
					this.types[node] === NodeType.Property &&
					A.textOf(Part.kind, node) === "init" &&
					!A.flag(Flag.method, node)
				) {
					this._spellProperty(node);
				}
				stack.pop();
				return;
			case NodeType.ObjectPattern:
			case NodeType.ArrayPattern:
			case NodeType.AssignmentPattern:
			case NodeType.RestElement:
				this._visitBinding(node, 0);
				return;
			case NodeType.TemplateLiteral:
				// Its strings, between the expressions, read nothing.
				stack.push(node);
				this._visitList(Field.expressions, node);
				stack.pop();
				return;
			case NodeType.ImportExpression:
				stack.push(node);
				this._visitChild(Field.source, node);
				this._visitChild(Field.options, node);
				stack.pop();
				return;
			case NodeType.MethodDefinition:
				if (
					A.type(A.field(0, Field.key, node)) === NodeType.PrivateIdentifier
				) {
					this.namesPrivate = true;
				}
				stack.push(node);
				if (A.flag(Flag.computed, node)) this._visitChild(Field.key, node);
				this._visitChild(Field.value, node);
				stack.pop();
				return;
			case NodeType.IfStatement:
			case NodeType.ConditionalExpression:
				stack.push(node);
				this._visitChild(Field.test, node);
				this._visitChild(Field.consequent, node);
				this._visitChild(Field.alternate, node);
				stack.pop();
				return;
			case NodeType.SwitchCase:
				stack.push(node);
				this._visitChild(Field.test, node);
				this._visitList(Field.consequent, node);
				stack.pop();
				return;
			case NodeType.ArrayExpression:
				stack.push(node);
				this._visitList(Field.elements, node);
				stack.pop();
				return;
			case NodeType.ObjectExpression:
				stack.push(node);
				this._visitList(Field.properties, node);
				stack.pop();
				return;
			case NodeType.SequenceExpression:
				stack.push(node);
				this._visitList(Field.expressions, node);
				stack.pop();
				return;
			case NodeType.TaggedTemplateExpression:
				stack.push(node);
				this._visitChild(Field.tag, node);
				this._visitChild(Field.quasi, node);
				stack.pop();
				return;
			case NodeType.ChainExpression:
				stack.push(node);
				this._visitChild(Field.expression, node);
				stack.pop();
				return;
			case NodeType.TryStatement:
				stack.push(node);
				this._visitChild(Field.block, node);
				this._visitChild(Field.handler, node);
				this._visitChild(Field.finalizer, node);
				stack.pop();
				return;
			case NodeType.PrivateIdentifier:
				this.namesPrivate = true;
				return;
			case NodeType.ImportDeclaration: {
				this._checkModuleStatement(node, "Import");
				stack.push(node);
				const count = A.fieldCount(Field.specifiers, node);
				for (let i = 0; i < count; i++) {
					const specifier = A.field(i, Field.specifiers, node);
					const local = A.field(0, Field.local, specifier);
					// terser holds a default import's name with no node around it.
					if (this.types[specifier] === NodeType.ImportDefaultSpecifier) {
						this._declare(local, DECLARES_IMPORT);
						continue;
					}
					stack.push(specifier);
					this._declare(local, DECLARES_IMPORT);
					if (this.types[specifier] === NodeType.ImportSpecifier) {
						this._spell(
							local,
							A.field(0, Field.imported, specifier),
							AS_SAVING
						);
					}
					stack.pop();
				}
				stack.pop();
				return;
			}
			case NodeType.ExportNamedDeclaration: {
				this._checkModuleStatement(node, "Export");
				stack.push(node);
				this._visitChild(Field.declaration, node);
				const flags =
					A.field(0, Field.source, node) !== 0
						? REFERENCE_EXPORTED | REFERENCE_FROM_MODULE
						: REFERENCE_EXPORTED;
				const count = A.fieldCount(Field.specifiers, node);
				for (let i = 0; i < count; i++) {
					const specifier = A.field(i, Field.specifiers, node);
					stack.push(specifier);
					const local = A.field(0, Field.local, specifier);
					this._addReference(local, flags);
					if ((flags & REFERENCE_FROM_MODULE) === 0) {
						this._spell(
							local,
							A.field(0, Field.exported, specifier),
							AS_SAVING
						);
					}
					stack.pop();
				}
				stack.pop();
				return;
			}
			case NodeType.ExportDefaultDeclaration:
				this._checkModuleStatement(node, "Export");
				stack.push(node);
				this._visitChild(Field.declaration, node);
				stack.pop();
				return;
			case NodeType.ExportAllDeclaration:
				// terser's `*` reads a global no name in the output depends on.
				this._checkModuleStatement(node, "Export");
				return;
			case NodeType.Super:
			case NodeType.EmptyStatement:
			case NodeType.DebuggerStatement:
			case NodeType.MetaProperty:
				return;
			default:
				throw new Error(
					`The minifier's scope analysis cannot read a node of type ${type}`
				);
		}
	}

	/**
	 * Resolves each name read, finds `eval`, and encloses what a catch
	 * parameter redefines.
	 * @returns {void}
	 */
	_resolve() {
		const { referenceNodes, referenceScopes, referenceFlags, globals } = this;
		for (let i = 0; i < referenceNodes.length; i++) {
			const node = referenceNodes[i];
			const from = referenceScopes[i];
			const flags = referenceFlags[i];
			if (flags & REFERENCE_CATCH) {
				const redefinition = /** @type {MinifierVariable | undefined} */ (
					from.variableScope.getBinding(A.name(node))
				);
				if (redefinition !== undefined) encloseVariable(from, redefinition);
				continue;
			}
			const name = this._nameOf(node);
			if (flags & REFERENCE_CALLED) {
				for (
					let outer = /** @type {MinifierScope | null} */ (from);
					outer !== null && !outer.usesEval;
					outer = /** @type {MinifierScope | null} */ (outer.upper)
				) {
					outer.usesEval = true;
				}
			}
			let variable =
				flags & REFERENCE_FROM_MODULE
					? undefined
					: findMinifierVariable(from, name, i);
			if (variable === undefined) {
				variable = globals.get(name);
				if (variable === undefined) {
					variable = new MinifierVariable(name, this.toplevel, DECLARES_GLOBAL);
					variable.undeclared = true;
					variable.global = true;
					globals.set(name, variable);
				}
				if (flags & REFERENCE_EXPORTED) variable.export = EXPORT_KEEP_NAME;
			}
			if (A.type(node) === NodeType.Identifier) {
				if (flags & REFERENCE_WRITTEN) {
					variable.written = true;
					variable.writes++;
				}
				this.definitions[node] = variable;
				this._referenceVariable(from, variable);
				this._recordCatchRead(node, from, variable);
			} else {
				// A re-exported string reads a global, which keeps no references.
				encloseVariable(from, variable);
			}
		}
		const { parameterRanges } = this;
		for (let i = 0; i < parameterRanges.length; i++) {
			parameterRanges[i].parameterStart = -1;
			parameterRanges[i].parameterEnd = -1;
		}
		if (this.catchReads !== null) this._moveCatchParameters();
		// terser's pass 4, up to the function: a block around the loop that the
		// one pass prints without braces leaves the loop in the scope outside.
		const { forScopes } = this;
		for (let i = 0; i < forScopes.length; i++) {
			const forScope = forScopes[i];
			let outer = /** @type {MinifierScope} */ (forScope.upper);
			for (;;) {
				const { variables } = outer;
				for (let j = 0; j < variables.length; j++) {
					encloseUnique(
						forScope,
						/** @type {MinifierVariable} */ (variables[j])
					);
				}
				if (outer === forScope.variableScope) break;
				outer = /** @type {MinifierScope} */ (outer.upper);
			}
		}
	}

	/**
	 * terser's pass 3 under `ie8` or `safari10`: each catch parameter, and every
	 * name resolved to it, is its function's definition of the name, which the
	 * parameter writes, so the mangler names the two alike.
	 * @returns {void}
	 */
	_moveCatchParameters() {
		const { catchNames, catchScopes, definitions, globals } = this;
		const catchReads =
			/** @type {Map<MinifierVariable, { nodes: number[], scopes: MinifierScope[] }>} */ (
				this.catchReads
			);
		for (let i = 0; i < catchNames.length; i++) {
			const identifier = catchNames[i];
			const name = A.name(identifier);
			const defunScope = /** @type {MinifierScope} */ (
				catchScopes[i].variableScope
			);
			const variable =
				findMinifierVariable(defunScope, name) ||
				globals.get(name) ||
				this._defineVariable(defunScope, 0, name, DECLARES_CATCH);
			variable.written = true;
			variable.writes++;
			const reads = catchReads.get(
				/** @type {MinifierVariable} */ (definitions[identifier])
			);
			if (reads !== undefined) {
				const { nodes, scopes } = reads;
				for (let j = 0; j < nodes.length; j++) {
					definitions[nodes[j]] = variable;
					this._referenceVariable(scopes[j], variable);
				}
			}
			definitions[identifier] = variable;
			this._referenceVariable(catchScopes[i], variable);
		}
	}

	/**
	 * Points each read of a `let`, `const` or body's `var` set to a name nothing writes at
	 * that name, terser's `reduce_vars`: the mangler then keeps the scopes
	 * between from naming anything else so, and the alias goes unread.
	 * @returns {number[]} the declarators whose name no read reads any more
	 */
	_substituteAliases() {
		const { referenceNodes, referenceScopes, referenceFlags, definitions } =
			this;
		/** @type {Map<MinifierVariable, MinifierVariable>} */
		const targets = new Map();
		/** @type {number[]} */
		const declarators = [];
		/** @type {Map<MinifierVariable, number>} */
		const varEnds = new Map();
		// The scopes reading `arguments`, which may write a parameter.
		/** @type {Set<Scope>} */
		const readArguments = new Set();
		for (let i = 0; i < referenceNodes.length; i++) {
			if (A.name(referenceNodes[i]) !== "arguments") continue;
			for (
				let scope = /** @type {Scope | null} */ (referenceScopes[i]);
				scope !== null;
				scope = scope.upper
			) {
				readArguments.add(scope);
			}
		}
		for (const declarator of /** @type {number[]} */ (this.aliasDeclarators)) {
			const alias = definitions[A.field(0, Field.id, declarator)];
			const target = definitions[this._child(Field.init, declarator)];
			if (
				isMinifierVariable(alias) &&
				isMinifierVariable(target) &&
				alias !== target &&
				!alias.written &&
				// A `var` alias read more often, or for a longer name, saves only its
				// declarator, which compressed the names read instead give back.
				(alias.kind !== DECLARES_VAR ||
					(alias.referenceCount <= 1 &&
						target.name.length <= alias.name.length)) &&
				// What an `export` names is toplevel, so never an alias here.
				!alias.global &&
				alias.export === 0 &&
				alias.declarations === 1 << alias.kind &&
				!(/** @type {MinifierScope} */ (alias.scope).isPinned()) &&
				!target.written &&
				!target.global &&
				!target.undeclared &&
				target.declarations === 1 << target.kind &&
				(target.kind === DECLARES_LET ||
					target.kind === DECLARES_CONST ||
					(target.kind === DECLARES_FUNARG &&
						!readArguments.has(/** @type {MinifierScope} */ (target.scope)))) &&
				!(/** @type {MinifierScope} */ (target.scope).isPinned()) &&
				encloses(
					/** @type {MinifierScope} */ (target.scope),
					/** @type {MinifierScope} */ (alias.scope)
				)
			) {
				targets.set(alias, target);
				declarators.push(declarator);
				if (alias.kind === DECLARES_VAR) {
					varEnds.set(alias, A.end(declarator));
				}
			}
		}
		// A `var` reads `undefined` before its declarator runs, and in a function
		// that may run first: each read must follow it in its own function.
		if (varEnds.size !== 0) {
			for (let i = 0; i < referenceNodes.length; i++) {
				const alias = /** @type {MinifierVariable} */ (
					definitions[referenceNodes[i]]
				);
				const end = varEnds.get(alias);
				if (
					end !== undefined &&
					(referenceScopes[i].variableScope !==
						/** @type {MinifierScope} */ (alias.scope).variableScope ||
						A.start(referenceNodes[i]) < end)
				) {
					targets.delete(alias);
				}
			}
		}
		if (targets.size === 0) return [];
		// A cycle, `const a = b, b = a`, has no name at its end to read.
		/** @type {MinifierVariable[]} */
		const cyclic = [];
		for (const [alias, target] of targets) {
			let next = /** @type {MinifierVariable | undefined} */ (target);
			for (let steps = 0; next !== undefined; steps++) {
				if (steps === targets.size) {
					cyclic.push(alias);
					break;
				}
				next = targets.get(next);
			}
		}
		for (const alias of cyclic) targets.delete(alias);
		/**
		 * @param {MinifierVariable} alias an alias
		 * @returns {MinifierVariable | undefined} the name at the end of its chain
		 */
		const targetOf = (alias) => {
			let target = targets.get(alias);
			if (target === undefined) return;
			for (
				let next = targets.get(target);
				next !== undefined;
				next = targets.get(next)
			) {
				target = next;
			}
			return target;
		};
		// A read where a scope between declares the target's name stays the
		// alias's; dropping one alias moves the end of chains through it.
		for (let dropped = true; dropped && targets.size !== 0;) {
			dropped = false;
			for (let i = 0; i < referenceNodes.length; i++) {
				if (referenceFlags[i] & REFERENCE_CATCH) continue;
				const alias = /** @type {MinifierVariable} */ (
					definitions[referenceNodes[i]]
				);
				const target = targetOf(alias);
				if (target !== undefined && shadowedFrom(referenceScopes[i], target)) {
					targets.delete(alias);
					dropped = true;
				}
			}
		}
		for (let i = 0; i < referenceNodes.length; i++) {
			const node = referenceNodes[i];
			if (referenceFlags[i] & REFERENCE_CATCH) continue;
			const alias = /** @type {MinifierVariable} */ (definitions[node]);
			const target = targetOf(alias);
			if (target === undefined) continue;
			definitions[node] = target;
			alias.referenceCount--;
			this._referenceVariable(referenceScopes[i], target);
		}
		return declarators.filter((declarator) =>
			targets.has(
				/** @type {MinifierVariable} */ (
					definitions[A.field(0, Field.id, declarator)]
				)
			)
		);
	}

	/**
	 * A `var` read in a nested function is set by then where that function,
	 * the outermost between, is an expression made after the declarator.
	 * @param {MinifierScope} scope the scope of a read in a nested function
	 * @param {MinifierVariable} definition the `var` it reads
	 * @param {number} declarator the declarator setting it
	 * @param {number} init the function it is set to
	 * @returns {boolean} whether the read runs only after the declarator ran, the function's body one statement its call may print as
	 */
	_madeAfter(scope, definition, declarator, init) {
		// WHY: a longer body moved stays a function, made at each call there,
		// and the names after it shift, which deflate codes in more.
		if (A.fieldCount(Field.body, this._child(Field.body, init)) !== 1) {
			return false;
		}
		// Its own name reads the function made at that call, a new one each time.
		if (
			this.types[init] === NodeType.FunctionExpression &&
			A.field(0, Field.id, init) !== 0
		) {
			return false;
		}
		const home = /** @type {MinifierScope} */ (definition.scope).variableScope;
		let outer = /** @type {MinifierScope} */ (scope.variableScope);
		while (outer.upper !== null && outer.upper.variableScope !== home) {
			outer = /** @type {MinifierScope} */ (outer.upper.variableScope);
		}
		const type = this.types[outer.node];
		return (
			outer.upper !== null &&
			(type === NodeType.FunctionExpression ||
				type === NodeType.ArrowFunctionExpression) &&
			A.start(outer.node) >= A.end(declarator)
		);
	}

	/**
	 * @param {number} fn a function
	 * @returns {boolean} whether it takes no parameters nor reads its own `this` or `arguments`, its body one `return` of a value or an arrow's expression
	 */
	_returnsOnly(fn) {
		if (A.fieldCount(Field.params, fn) !== 0) return false;
		// Its own `this` or `arguments` keeps the call a call.
		if (this.types[fn] !== NodeType.ArrowFunctionExpression) {
			for (const start of /** @type {number[]} */ (this.thisStarts)) {
				if (start >= A.start(fn) && start < A.end(fn)) return false;
			}
		}
		const body = this._child(Field.body, fn);
		if (this.types[body] !== NodeType.BlockStatement) return true;
		if (A.fieldCount(Field.body, body) !== 1) return false;
		const statement = A.field(0, Field.body, body);
		return (
			this.types[statement] === NodeType.ReturnStatement &&
			A.field(0, Field.argument, statement) !== 0
		);
	}

	/**
	 * Moves each function a declarator names and one read reads to that read,
	 * terser's single use: the read is in the same function, after it in the
	 * statements listing it and in no loop it is not in, making one function.
	 * @returns {number[]} each declarator and its read, in pairs
	 */
	_moveFunctions() {
		const { referenceNodes, referenceScopes, referenceFlags, definitions } =
			this;
		/** @type {Map<MinifierVariable, number>} */
		const candidates = new Map();
		const bindings = /** @type {number[]} */ (this.functionBindings);
		/** @type {Map<number, number>} */
		const lists = new Map();
		for (let i = 0; i < bindings.length; i += 3) {
			const declarator = bindings[i];
			lists.set(declarator, i);
			const definition = definitions[A.field(0, Field.id, declarator)];
			// A declared function reads as made where its list starts.
			if (this.types[declarator] === NodeType.FunctionDeclaration) {
				bindings[i + 2] = Infinity;
			}
			if (
				isMinifierVariable(definition) &&
				definition.referenceCount === 1 &&
				!definition.written &&
				(!definition.global || this.movesToplevel) &&
				definition.export === 0 &&
				definition.declarations === 1 << definition.kind &&
				!(/** @type {MinifierScope} */ (definition.scope).isPinned())
			) {
				candidates.set(definition, declarator);
			}
		}
		/** @type {number[]} */
		const moved = [];
		if (candidates.size === 0) return moved;
		// Each candidate's one read, for a pair of functions reading each other.
		/** @type {Map<MinifierVariable, number>} */
		const reads = new Map();
		for (const node of referenceNodes) {
			const definition = /** @type {MinifierVariable} */ (definitions[node]);
			if (candidates.has(definition)) reads.set(definition, node);
		}
		// Per move: the function, the scope reading it and its definition.
		/** @type {number[]} */
		const movedInits = [];
		/** @type {MinifierScope[]} */
		const movedScopes = [];
		/** @type {MinifierVariable[]} */
		const movedDefinitions = [];
		// Each move's read, which prints the function rather than its name.
		/** @type {Map<number, number>} */
		const movedReads = new Map();
		const loops = /** @type {number[]} */ (this.loopRanges);
		/** @type {number[] | undefined} */
		let byStart;
		// By candidate, the candidate innermost holding its one read.
		/** @type {Map<MinifierVariable, MinifierVariable | null>} */
		const holders = new Map();
		/**
		 * @param {MinifierVariable} definition a candidate
		 * @returns {MinifierVariable | null} the candidate whose function innermost holds its one read
		 */
		const holderOf = (definition) => {
			const known = holders.get(definition);
			if (known !== undefined) return known;
			const read = reads.get(definition);
			/** @type {MinifierVariable | null} */
			let holder = null;
			let holderStart = -1;
			if (read !== undefined) {
				for (const [other, otherDeclarator] of candidates) {
					if (other === definition) continue;
					const otherInit =
						this.types[otherDeclarator] === NodeType.FunctionDeclaration
							? otherDeclarator
							: this._child(Field.init, otherDeclarator);
					if (
						A.start(otherInit) > holderStart &&
						A.start(otherInit) <= A.start(read) &&
						A.end(read) <= A.end(otherInit)
					) {
						holder = other;
						holderStart = A.start(otherInit);
					}
				}
			}
			holders.set(definition, holder);
			return holder;
		};
		for (let i = 0; i < referenceNodes.length; i++) {
			const node = referenceNodes[i];
			const definition = /** @type {MinifierVariable} */ (definitions[node]);
			const declarator = candidates.get(definition);
			if (
				declarator === undefined ||
				referenceFlags[i] & (REFERENCE_EXPORTED | REFERENCE_CATCH)
			) {
				continue;
			}
			const scope = referenceScopes[i];
			const init =
				this.types[declarator] === NodeType.FunctionDeclaration
					? declarator
					: this._child(Field.init, declarator);
			if (
				(scope.variableScope !==
					/** @type {MinifierScope} */ (definition.scope).variableScope &&
					// Called, a function of its own `this` shows no other place.
					((referenceFlags[i] & REFERENCE_CALLEE) === 0 ||
						this.types[init] === NodeType.ArrowFunctionExpression ||
						(definition.kind === DECLARES_VAR &&
							!this._madeAfter(scope, definition, declarator, init)))) ||
				(this.types[declarator] === NodeType.FunctionDeclaration
					? // Hoisted, it is made before any read but its own.
						A.start(node) >= A.start(init) && A.end(node) <= A.end(init)
					: A.start(node) < A.end(init)) ||
				// Only a read the statements listing it reach runs after it.
				A.end(node) >
					bindings[/** @type {number} */ (lists.get(declarator)) + 2] ||
				// A call of one returning a value prints as that value there.
				(entersLoop(
					loops,
					Math.min(
						A.start(declarator),
						bindings[/** @type {number} */ (lists.get(declarator)) + 1]
					),
					A.start(node),
					A.end(node)
				) &&
					((referenceFlags[i] & REFERENCE_CALLED_BARE) === 0 ||
						!this._returnsOnly(init)))
			) {
				continue;
			}
			// Moved into a function its own body reads, through any chain of
			// functions read once in each other, a dead cycle would read itself.
			let cycles = false;
			for (
				let holder = holderOf(definition), steps = candidates.size;
				holder !== null && steps-- > 0;
				holder = holderOf(holder)
			) {
				if (holder === definition) {
					cycles = true;
					break;
				}
			}
			if (cycles) continue;
			// What it reads from outside is read from the read's place now.
			if (byStart === undefined) {
				byStart = referencesByStart(referenceNodes);
			}
			const start = A.start(init);
			const end = A.end(init);
			if (
				scope.variableScope !==
				/** @type {MinifierScope} */ (definition.scope).variableScope
			) {
				let readsArguments = false;
				for (
					let j = firstFrom(byStart, referenceNodes, start);
					j < byStart.length && A.start(referenceNodes[byStart[j]]) < end;
					j++
				) {
					const read = definitions[referenceNodes[byStart[j]]];
					// Its `arguments.callee` would show a new function each call there.
					if (
						isMinifierVariable(read) &&
						read.kind === DECLARES_FUNARG &&
						/** @type {MinifierScope} */ (read.scope).node === init &&
						A.name(referenceNodes[byStart[j]]) === "arguments"
					) {
						readsArguments = true;
						break;
					}
				}
				if (readsArguments) continue;
			}
			let shadowed = false;
			for (
				let j = firstFrom(byStart, referenceNodes, start);
				j < byStart.length && A.start(referenceNodes[byStart[j]]) < end;
				j++
			) {
				if (movedReads.has(referenceNodes[byStart[j]])) continue;
				const read = definitions[referenceNodes[byStart[j]]];
				if (
					isMinifierVariable(read) &&
					encloses(
						/** @type {MinifierScope} */ (read.scope),
						/** @type {MinifierScope} */ (definition.scope)
					) &&
					shadowedFrom(scope, read)
				) {
					shadowed = true;
					break;
				}
			}
			if (shadowed) continue;
			for (
				let j = firstFrom(byStart, referenceNodes, start);
				j < byStart.length && A.start(referenceNodes[byStart[j]]) < end;
				j++
			) {
				const read = definitions[referenceNodes[byStart[j]]];
				if (
					isMinifierVariable(read) &&
					encloses(
						/** @type {MinifierScope} */ (read.scope),
						/** @type {MinifierScope} */ (definition.scope)
					)
				) {
					encloseVariable(scope, read);
				}
			}
			definition.referenceCount = 0;
			movedReads.set(node, moved.length);
			moved.push(declarator, node);
			movedInits.push(init);
			movedScopes.push(scope);
			movedDefinitions.push(definition);
		}
		// A function moved into one that moves too prints where that one does:
		// a name declared there shadowing what it reads keeps it in place.
		const kept = new Uint8Array(moved.length >> 1);
		for (let changed = true; changed;) {
			changed = false;
			for (let k = 0; k < moved.length; k += 2) {
				if (kept[k >> 1] === 1) continue;
				const init = movedInits[k >> 1];
				const definition = movedDefinitions[k >> 1];
				if (
					this._readsKeptShadowed(
						init,
						definition,
						movedScopes[k >> 1],
						/** @type {number[]} */ (byStart),
						movedReads,
						kept
					)
				) {
					kept[k >> 1] = 1;
					definition.referenceCount = 1;
					changed = true;
					continue;
				}
				for (let at = moved[k + 1], steps = moved.length; steps-- > 0;) {
					let holder = -1;
					for (let m = 0; m < moved.length; m += 2) {
						const outer = movedInits[m >> 1];
						if (
							m !== k &&
							kept[m >> 1] === 0 &&
							A.start(outer) <= A.start(at) &&
							A.end(at) <= A.end(outer)
						) {
							holder = m;
							break;
						}
					}
					if (holder === -1) break;
					if (
						this._readsShadowed(
							init,
							definition,
							movedScopes[holder >> 1],
							/** @type {number[]} */ (byStart)
						)
					) {
						kept[k >> 1] = 1;
						definition.referenceCount = 1;
						changed = true;
						break;
					}
					at = moved[holder + 1];
				}
			}
		}
		let count = 0;
		for (let k = 0; k < moved.length; k += 2) {
			if (kept[k >> 1] === 1) continue;
			moved[count] = moved[k];
			moved[count + 1] = moved[k + 1];
			movedInits[count >> 1] = movedInits[k >> 1];
			movedScopes[count >> 1] = movedScopes[k >> 1];
			movedDefinitions[count >> 1] = movedDefinitions[k >> 1];
			count += 2;
		}
		moved.length = count;
		// What it reads from outside is read from there as well.
		for (let k = 0; k < moved.length; k += 2) {
			const init = movedInits[k >> 1];
			const start = A.start(init);
			const end = A.end(init);
			const definition = movedDefinitions[k >> 1];
			// Bounded, as two functions may each read the other once.
			for (let at = moved[k + 1], steps = moved.length; steps-- > 0;) {
				let holder = -1;
				for (let m = 0; m < moved.length; m += 2) {
					const outer = movedInits[m >> 1];
					if (
						m !== k &&
						A.start(outer) <= A.start(at) &&
						A.end(at) <= A.end(outer)
					) {
						holder = m;
						break;
					}
				}
				if (holder === -1) break;
				for (
					let j = firstFrom(
						/** @type {number[]} */ (byStart),
						referenceNodes,
						start
					);
					j < /** @type {number[]} */ (byStart).length &&
					A.start(referenceNodes[/** @type {number[]} */ (byStart)[j]]) < end;
					j++
				) {
					const read =
						definitions[referenceNodes[/** @type {number[]} */ (byStart)[j]]];
					if (
						isMinifierVariable(read) &&
						encloses(
							/** @type {MinifierScope} */ (read.scope),
							/** @type {MinifierScope} */ (definition.scope)
						)
					) {
						encloseVariable(movedScopes[holder >> 1], read);
					}
				}
				at = moved[holder + 1];
			}
		}
		return moved;
	}

	/**
	 * @param {number} init a function moving to its one read
	 * @param {MinifierVariable} definition the name it is declared by
	 * @param {MinifierScope} scope the scope it would be read from
	 * @param {number[]} byStart the references, ordered by where they start
	 * @returns {boolean} whether a name declared from that scope out shadows one it reads from outside
	 */
	_readsShadowed(init, definition, scope, byStart) {
		const { referenceNodes, definitions } = this;
		const end = A.end(init);
		for (
			let j = firstFrom(byStart, referenceNodes, A.start(init));
			j < byStart.length && A.start(referenceNodes[byStart[j]]) < end;
			j++
		) {
			const read = definitions[referenceNodes[byStart[j]]];
			if (
				isMinifierVariable(read) &&
				encloses(
					/** @type {MinifierScope} */ (read.scope),
					/** @type {MinifierScope} */ (definition.scope)
				) &&
				shadowedFrom(scope, read)
			) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @param {number} init a function moved
	 * @param {MinifierVariable} definition its name's definition
	 * @param {MinifierScope} scope the scope of its read
	 * @param {number[]} byStart the indexes of the names read, ordered by start
	 * @param {Map<number, number>} movedReads each move's read and that move's index
	 * @param {Uint8Array} kept by move, 1 for one kept in place
	 * @returns {boolean} whether it holds the read of a function kept in place, whose name is shadowed there
	 */
	_readsKeptShadowed(init, definition, scope, byStart, movedReads, kept) {
		const { referenceNodes, definitions } = this;
		const end = A.end(init);
		for (
			let j = firstFrom(byStart, referenceNodes, A.start(init));
			j < byStart.length && A.start(referenceNodes[byStart[j]]) < end;
			j++
		) {
			const index = movedReads.get(referenceNodes[byStart[j]]);
			if (index === undefined || kept[index >> 1] === 0) continue;
			const read = definitions[referenceNodes[byStart[j]]];
			if (
				isMinifierVariable(read) &&
				encloses(
					/** @type {MinifierScope} */ (read.scope),
					/** @type {MinifierScope} */ (definition.scope)
				) &&
				shadowedFrom(scope, read)
			) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @param {number[]} identifiers names
	 * @returns {NamedIdentifier[]} each as the mangler reads it: its name and its definition
	 */
	_asNames(identifiers) {
		return identifiers.map((identifier) => ({
			name: A.name(identifier),
			definition: this.definitions[identifier]
		}));
	}
}

/**
 * Analyses the tree `A` reads as `analyzeMinifierScope` does terser's tree of
 * the same source.
 * @param {number} program its program
 * @param {Uint8Array} types each node's type, as terser's tree types it
 * @param {MinifierScopeOptions} options the mangle options
 * @param {(node: number, message: string) => never} raise throws the parse error a misplaced import or export is
 * @returns {MinifierTreeScopeAnalysis} the scopes, and each name's definition
 */
const analyzeMinifierTree = (program, types, options, raise) => {
	if (listsStatements === undefined) {
		listsStatements = new Uint8Array(256);
		for (const type of [
			NodeType.Program,
			NodeType.BlockStatement,
			NodeType.StaticBlock,
			NodeType.SwitchCase,
			// A function's body is read without a node of its own.
			NodeType.FunctionDeclaration,
			NodeType.FunctionExpression,
			NodeType.ArrowFunctionExpression
		]) {
			listsStatements[type] = 1;
		}
	}
	const analyzer = new MinifierTreeScopeAnalyzer(
		program,
		types,
		options,
		raise
	);
	analyzer.stack.push(program);
	analyzer._visitList(Field.body, program);
	analyzer.stack.pop();
	analyzer._resolve();
	const { functionDeclarators, classDeclarators } = analyzer;
	const aliases =
		analyzer.aliasDeclarators === null ? null : analyzer._substituteAliases();
	// A catch parameter moved to its function shares its name with the
	// function's own, so a function moved into the catch would read it.
	const movedFunctions =
		analyzer.functionBindings === null ||
		analyzer.catchNames.length !== 0 ||
		options.movesFunctions === false
			? null
			: analyzer._moveFunctions();
	return {
		aliases,
		movedFunctions,
		toplevel: analyzer.toplevel,
		labels: analyzer.labels,
		globals: analyzer.globals,
		blockDefunScopes: analyzer.blockDefunScopes,
		functionDeclarators:
			functionDeclarators === null
				? null
				: analyzer._asNames(functionDeclarators),
		classDeclarators:
			classDeclarators === null ? null : analyzer._asNames(classDeclarators),
		catchParameters: analyzer._asNames(analyzer.catchParameters),
		namesPrivate: analyzer.namesPrivate,
		spelledNames: analyzer._spelledNames(),
		definitions: analyzer.definitions
	};
};

analyzeScope.Reference = Reference;
analyzeScope.ScopeIdentifier = ScopeIdentifier;
analyzeScope.Scope = Scope;
analyzeScope.Variable = Variable;
analyzeScope.MinifierLabel = MinifierLabel;
analyzeScope.MinifierScope = MinifierScope;
analyzeScope.MinifierVariable = MinifierVariable;
analyzeScope.isMinifierVariable = isMinifierVariable;
analyzeScope.analyzeMinifierTree = analyzeMinifierTree;
analyzeScope.encloseUnique = encloseUnique;
analyzeScope.DECLARES_VAR = DECLARES_VAR;
analyzeScope.DECLARES_FUNARG = DECLARES_FUNARG;
analyzeScope.DECLARES_LET = DECLARES_LET;
analyzeScope.DECLARES_CONST = DECLARES_CONST;
analyzeScope.DECLARES_USING = DECLARES_USING;
analyzeScope.DECLARES_CATCH = DECLARES_CATCH;
analyzeScope.DECLARES_IMPORT = DECLARES_IMPORT;
analyzeScope.DECLARES_DEFUN = DECLARES_DEFUN;
analyzeScope.DECLARES_LAMBDA = DECLARES_LAMBDA;
analyzeScope.DECLARES_CLASS = DECLARES_CLASS;
analyzeScope.DECLARES_DEF_CLASS = DECLARES_DEF_CLASS;
analyzeScope.DECLARES_GLOBAL = DECLARES_GLOBAL;
analyzeScope.EXPORT_KEEP_NAME = EXPORT_KEEP_NAME;
analyzeScope.EXPORT_WANT_MANGLE = EXPORT_WANT_MANGLE;

module.exports = analyzeScope;
