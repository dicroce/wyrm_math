/**
 * Immutable expression AST.
 *
 * Invariants (maintained by the smart constructors, relied on everywhere):
 *  - A Sum never contains a direct Sum child; a Product never contains a
 *    direct Product child (auto-flatten).
 *  - No Neg(Neg(x)) — double negation collapses to x.
 *  - Sum/Product always have >= 2 children. Constructing with 0 children
 *    yields the identity literal (0 / 1); with 1 child yields the child.
 *  - Integer.value >= 0. Negative literals are canonically Neg(Integer).
 *  - Every node has a stable, tree-unique id. Operations that rebuild a
 *    tree must preserve the ids of untouched subtrees (use the
 *    *-PreservingId helpers, never re-create nodes you didn't change).
 */

export type NodeId = string;

let idCounter = 0;
export function freshId(): NodeId {
  return `n${++idCounter}`;
}

export interface Integer {
  readonly kind: "int";
  readonly id: NodeId;
  /** Always >= 0; negative values are represented as Neg(Integer). */
  readonly value: bigint;
}

export interface Variable {
  readonly kind: "var";
  readonly id: NodeId;
  readonly name: string;
}

export interface Sum {
  readonly kind: "sum";
  readonly id: NodeId;
  /** N-ary; never contains a direct Sum child; length >= 2. */
  readonly children: readonly Expr[];
}

export interface Product {
  readonly kind: "product";
  readonly id: NodeId;
  /** N-ary; never contains a direct Product child; length >= 2. */
  readonly children: readonly Expr[];
}

export interface Neg {
  readonly kind: "neg";
  readonly id: NodeId;
  /** Never itself a Neg. */
  readonly child: Expr;
}

export interface Fraction {
  readonly kind: "fraction";
  readonly id: NodeId;
  /** Implicit products; an empty list means 1. */
  readonly num: readonly Expr[];
  readonly den: readonly Expr[];
}

export interface Pow {
  readonly kind: "pow";
  readonly id: NodeId;
  readonly base: Expr;
  readonly exp: Expr;
}

export interface Sqrt {
  readonly kind: "sqrt";
  readonly id: NodeId;
  readonly child: Expr;
}

/** The relation between the two sides. Inequalities are first-class. */
export type RelationKind = "=" | "<" | "≤" | ">" | "≥";

/** a R b ⇔ b flip(R) a; also what multiplying by a negative does. */
export function flipRelation(r: RelationKind): RelationKind {
  switch (r) {
    case "=":
      return "=";
    case "<":
      return ">";
    case "≤":
      return "≥";
    case ">":
      return "<";
    case "≥":
      return "≤";
  }
}

export interface Equation {
  readonly kind: "equation";
  readonly id: NodeId;
  readonly lhs: Expr;
  readonly rhs: Expr;
  readonly relation: RelationKind;
}

/** Expressions that can appear inside other expressions. */
export type Expr = Integer | Variable | Sum | Product | Neg | Fraction | Pow | Sqrt;
/** Anything addressable in a tree. Equation only ever appears at the root. */
export type Node = Expr | Equation;

// ---------------------------------------------------------------------------
// Smart constructors
// ---------------------------------------------------------------------------

/** Non-negative integer literal node. */
function rawInt(value: bigint): Integer {
  return { kind: "int", id: freshId(), value };
}

/** Integer literal; negative inputs canonicalize to Neg(Integer). */
export function int(value: bigint | number): Expr {
  const v = typeof value === "number" ? BigInt(value) : value;
  return v < 0n ? neg(rawInt(-v)) : rawInt(v);
}

export function variable(name: string): Variable {
  return { kind: "var", id: freshId(), name };
}

function flatten(kind: "sum" | "product", children: readonly Expr[]): Expr[] {
  return children.flatMap((c) => (c.kind === kind ? c.children : [c]));
}

/**
 * N-ary sum. Flattens direct Sum children; 0 children -> 0; 1 child -> the
 * child itself (id preserved).
 */
export function sum(children: readonly Expr[]): Expr {
  const flat = flatten("sum", children);
  if (flat.length === 0) return int(0);
  if (flat.length === 1) return flat[0]!;
  return { kind: "sum", id: freshId(), children: flat };
}

/**
 * N-ary product. Flattens direct Product children; 0 children -> 1; 1 child
 * -> the child itself (id preserved).
 */
export function product(children: readonly Expr[]): Expr {
  const flat = flatten("product", children);
  if (flat.length === 0) return int(1);
  if (flat.length === 1) return flat[0]!;
  return { kind: "product", id: freshId(), children: flat };
}

/** Negation; collapses Neg(Neg(x)) to x (x keeps its id). */
export function neg(child: Expr): Expr {
  if (child.kind === "neg") return child.child;
  return { kind: "neg", id: freshId(), child };
}

/**
 * Fraction lists are implicit products, so a direct Product element is a
 * redundant level (the same way Sum-in-Sum is): it auto-flattens, keeping
 * the product's children's ids.
 */
function flattenList(list: readonly Expr[]): Expr[] {
  return list.flatMap((e) => (e.kind === "product" ? e.children : [e]));
}

export function fraction(num: readonly Expr[], den: readonly Expr[]): Fraction {
  return { kind: "fraction", id: freshId(), num: flattenList(num), den: flattenList(den) };
}

export function pow(base: Expr, exp: Expr): Pow {
  return { kind: "pow", id: freshId(), base, exp };
}

export function sqrt(child: Expr): Sqrt {
  return { kind: "sqrt", id: freshId(), child };
}

export function equation(lhs: Expr, rhs: Expr, relation: RelationKind = "="): Equation {
  return { kind: "equation", id: freshId(), lhs, rhs, relation };
}

// ---------------------------------------------------------------------------
// Id-preserving rebuild helpers (for rewrite rules)
// ---------------------------------------------------------------------------

/**
 * Rebuild a Sum/Product around a new child list, keeping the original node's
 * id when the node survives. Collapses to the identity literal / single child
 * exactly like the smart constructors.
 */
export function rebuildNary(
  original: Sum | Product,
  children: readonly Expr[],
): Expr {
  const built =
    original.kind === "sum" ? sum(children) : product(children);
  if (built.kind === original.kind) {
    return { ...built, id: original.id };
  }
  return built;
}

/**
 * Replace the node with id `targetId` by `replacement`. All ancestors of the
 * target are rebuilt with their original ids; every other subtree is reused
 * untouched (same object identity, same ids).
 *
 * The caller is responsible for the replacement keeping the tree invariants
 * (e.g. don't put a Sum directly under a Sum). Throws if `targetId` is not in
 * the tree, or if the replacement of a child position would need to be an
 * Equation.
 */
export function replaceNode(
  root: Equation,
  targetId: NodeId,
  replacement: Expr,
): Equation {
  if (root.id === targetId) {
    throw new Error("replaceNode: cannot replace the Equation root with an Expr");
  }
  const lhs = replaceInExpr(root.lhs, targetId, replacement);
  const rhs = lhs !== root.lhs ? root.rhs : replaceInExpr(root.rhs, targetId, replacement);
  if (lhs === root.lhs && rhs === root.rhs) {
    throw new Error(`replaceNode: id ${targetId} not found in tree`);
  }
  return { ...root, lhs, rhs };
}

/** Returns the same object when the target is not in this subtree. */
function replaceInExpr(node: Expr, targetId: NodeId, replacement: Expr): Expr {
  if (node.id === targetId) return replacement;
  switch (node.kind) {
    case "int":
    case "var":
      return node;
    case "neg": {
      const child = replaceInExpr(node.child, targetId, replacement);
      return child === node.child ? node : { ...node, child };
    }
    case "sum":
    case "product": {
      const children = replaceAllIn(node.children, targetId, replacement);
      return children === node.children ? node : { ...node, children };
    }
    case "fraction": {
      const num = replaceAllIn(node.num, targetId, replacement);
      const den = replaceAllIn(node.den, targetId, replacement);
      return num === node.num && den === node.den ? node : { ...node, num, den };
    }
    case "pow": {
      const base = replaceInExpr(node.base, targetId, replacement);
      const exp = base !== node.base ? node.exp : replaceInExpr(node.exp, targetId, replacement);
      return base === node.base && exp === node.exp ? node : { ...node, base, exp };
    }
    case "sqrt": {
      const child = replaceInExpr(node.child, targetId, replacement);
      return child === node.child ? node : { ...node, child };
    }
  }
}

function replaceAllIn(
  list: readonly Expr[],
  targetId: NodeId,
  replacement: Expr,
): readonly Expr[] {
  let changed = false;
  const out = list.map((c) => {
    const r = replaceInExpr(c, targetId, replacement);
    if (r !== c) changed = true;
    return r;
  });
  return changed ? out : list;
}

/**
 * Like replaceNode, but repairs what a substitution can break at the splice
 * point: a Neg replacement under a Neg parent collapses both (no
 * Neg(Neg(x))), a Sum/Product replacement under a same-kind parent flattens
 * into it, and a Product replacement inside a Fraction list spreads into the
 * list (the lists ARE implicit products, and rules pair individual list
 * elements — a nested Product would strand its factors out of reach). One
 * level is always enough because the surrounding tree already satisfies the
 * invariants.
 */
export function replaceTermRespectingInvariants(
  root: Equation,
  targetId: NodeId,
  replacement: Expr,
): Equation {
  const parent = findParent(root, targetId);
  if (parent === undefined) {
    throw new Error(`replaceTermRespectingInvariants: id ${targetId} not found`);
  }
  if (parent.kind === "neg" && replacement.kind === "neg") {
    // Collapsing Neg(Neg(x)) surfaces x one level up — which is itself a
    // replacement that may need repair there (e.g. a Product surfacing into
    // a Fraction list). Recurse; depth strictly decreases.
    return replaceTermRespectingInvariants(root, parent.id, replacement.child);
  }
  if (
    (parent.kind === "sum" || parent.kind === "product") &&
    replacement.kind === parent.kind
  ) {
    const children = parent.children.flatMap((c) =>
      c.id === targetId ? replacement.children : [c],
    );
    return replaceNode(root, parent.id, rebuildNary(parent, children));
  }
  if (parent.kind === "fraction" && replacement.kind === "product") {
    const splice = (list: readonly Expr[]): Expr[] =>
      list.flatMap((c) => (c.id === targetId ? [...replacement.children] : [c]));
    return replaceNode(root, parent.id, {
      ...parent,
      num: splice(parent.num),
      den: splice(parent.den),
    });
  }
  return replaceNode(root, targetId, replacement);
}

/** Deep copy with all-new ids (for inserting a second copy of a subtree). */
export function cloneFresh(node: Expr): Expr {
  switch (node.kind) {
    case "int":
      return { ...node, id: freshId() };
    case "var":
      return { ...node, id: freshId() };
    case "neg":
      return { kind: "neg", id: freshId(), child: cloneFresh(node.child) };
    case "sum":
      return { kind: "sum", id: freshId(), children: node.children.map(cloneFresh) };
    case "product":
      return { kind: "product", id: freshId(), children: node.children.map(cloneFresh) };
    case "fraction":
      return {
        kind: "fraction",
        id: freshId(),
        num: node.num.map(cloneFresh),
        den: node.den.map(cloneFresh),
      };
    case "pow":
      return { kind: "pow", id: freshId(), base: cloneFresh(node.base), exp: cloneFresh(node.exp) };
    case "sqrt":
      return { kind: "sqrt", id: freshId(), child: cloneFresh(node.child) };
  }
}

// ---------------------------------------------------------------------------
// Traversal
// ---------------------------------------------------------------------------

/** Direct child expressions of a node, in display order. */
export function childrenOf(node: Node): readonly Expr[] {
  switch (node.kind) {
    case "int":
    case "var":
      return [];
    case "neg":
    case "sqrt":
      return [node.child];
    case "sum":
    case "product":
      return node.children;
    case "fraction":
      return [...node.num, ...node.den];
    case "pow":
      return [node.base, node.exp];
    case "equation":
      return [node.lhs, node.rhs];
  }
}

/** Pre-order traversal of every node in the tree (including the root). */
export function* allNodes(root: Node): Generator<Node> {
  yield root;
  for (const c of childrenOf(root)) yield* allNodes(c);
}

/** The node whose child list contains `id`, or undefined for the root / missing ids. */
export function findParent(root: Node, id: NodeId): Node | undefined {
  for (const n of allNodes(root)) {
    if (childrenOf(n).some((c) => c.id === id)) return n;
  }
  return undefined;
}

export function findById(root: Node, id: NodeId): Node | undefined {
  for (const n of allNodes(root)) if (n.id === id) return n;
  return undefined;
}

/** All variable names appearing in the tree. */
export function variablesIn(root: Node): Set<string> {
  const out = new Set<string>();
  for (const n of allNodes(root)) if (n.kind === "var") out.add(n.name);
  return out;
}

/** Compact debug/description rendering. Not a UI concern — UI does layout. */
export function exprToString(node: Node): string {
  switch (node.kind) {
    case "int":
      return `${node.value}`;
    case "var":
      return node.name;
    case "neg":
      return `-${exprToString(node.child)}`;
    case "sum":
      return `(${node.children.map(exprToString).join(" + ")})`;
    case "product":
      return `(${node.children.map(exprToString).join(" * ")})`;
    case "fraction": {
      const num = node.num.length === 0 ? "1" : node.num.map(exprToString).join(" * ");
      const den = node.den.length === 0 ? "1" : node.den.map(exprToString).join(" * ");
      return `((${num}) / (${den}))`;
    }
    case "pow": {
      // Neg and Pow bases need parens to read (and re-parse) unambiguously:
      // (-x)^2 is not -x^2; (a^b)^c is not a^b^c. Other kinds self-wrap.
      const base =
        node.base.kind === "neg" || node.base.kind === "pow"
          ? `(${exprToString(node.base)})`
          : exprToString(node.base);
      return `${base}^${exprToString(node.exp)}`;
    }
    case "sqrt":
      return `√(${exprToString(node.child)})`;
    case "equation":
      return `${exprToString(node.lhs)} ${node.relation} ${exprToString(node.rhs)}`;
  }
}

// ---------------------------------------------------------------------------
// Structural equality (commutative for Sum/Product, ignores ids)
// ---------------------------------------------------------------------------

/**
 * Structural equality. Ignores node ids. Sum and Product (and Fraction's
 * num/den lists, which are implicit products) compare their children as
 * multisets — order-insensitive. Equation sides are ordered (a=b ≠ b=a).
 */
export function eq(a: Node, b: Node): boolean {
  if (a === b) return true;
  if (a.kind !== b.kind) return false;
  switch (a.kind) {
    case "int":
      return a.value === (b as Integer).value;
    case "var":
      return a.name === (b as Variable).name;
    case "neg":
      return eq(a.child, (b as Neg).child);
    case "sqrt":
      return eq(a.child, (b as Sqrt).child);
    case "sum":
    case "product":
      return multisetEq(a.children, (b as Sum | Product).children);
    case "fraction": {
      const bf = b as Fraction;
      return multisetEq(a.num, bf.num) && multisetEq(a.den, bf.den);
    }
    case "pow": {
      const bp = b as Pow;
      return eq(a.base, bp.base) && eq(a.exp, bp.exp);
    }
    case "equation": {
      const be = b as Equation;
      return a.relation === be.relation && eq(a.lhs, be.lhs) && eq(a.rhs, be.rhs);
    }
  }
}

/**
 * Order-insensitive comparison. Greedy matching is correct here because eq is
 * an equivalence relation (equal elements are interchangeable).
 */
function multisetEq(as: readonly Expr[], bs: readonly Expr[]): boolean {
  if (as.length !== bs.length) return false;
  const used = new Array<boolean>(bs.length).fill(false);
  outer: for (const a of as) {
    for (let i = 0; i < bs.length; i++) {
      if (!used[i] && eq(a, bs[i]!)) {
        used[i] = true;
        continue outer;
      }
    }
    return false;
  }
  return true;
}

// ---------------------------------------------------------------------------
// Invariant checking (used by tests; cheap enough for debug assertions)
// ---------------------------------------------------------------------------

/** Returns a list of invariant violations (empty = healthy tree). */
export function invariantViolations(root: Node): string[] {
  const problems: string[] = [];
  const seen = new Set<NodeId>();
  for (const n of allNodes(root)) {
    if (seen.has(n.id)) problems.push(`duplicate id ${n.id} (${n.kind})`);
    seen.add(n.id);
    switch (n.kind) {
      case "int":
        if (n.value < 0n) problems.push(`negative Integer literal ${n.value}`);
        break;
      case "neg":
        if (n.child.kind === "neg") problems.push(`Neg(Neg(...)) at ${n.id}`);
        break;
      case "sum":
      case "product":
        if (n.children.length < 2)
          problems.push(`${n.kind} ${n.id} has ${n.children.length} children`);
        if (n.children.some((c) => c.kind === n.kind))
          problems.push(`${n.kind} ${n.id} contains a direct ${n.kind} child`);
        break;
      case "fraction":
        if ([...n.num, ...n.den].some((c) => c.kind === "product"))
          problems.push(`fraction ${n.id} contains a direct Product list element`);
        break;
      case "equation":
        if (n !== root) problems.push(`Equation ${n.id} below the root`);
        break;
      default:
        break;
    }
  }
  return problems;
}
