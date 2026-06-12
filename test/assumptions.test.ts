import { describe, expect, it } from "vitest";
import {
  AssumptionConflict,
  Derivation,
  divideBothSides,
  eq,
  equation,
  fraction,
  int,
  multiplicativeCancellation,
  Rational,
  RulePreconditionViolation,
  sum,
  variable,
  type Restriction,
} from "../src/index.js";

const envOf = (entries: [string, number][]) =>
  new Map(entries.map(([k, v]) => [k, Rational.of(v)] as const));

function xEquals3() {
  const eqn = equation(variable("x"), int(3));
  return { eqn, d: new Derivation(eqn) };
}

describe("assumption lifecycle", () => {
  it("discharges constant restrictions immediately — recorded, not deleted", () => {
    const { eqn, d } = xEquals3();
    const node = d.apply(divideBothSides, eqn.id, { divisor: int(2) });
    const r = d.current.assumptions.find((a) => a.kind === "restriction") as Restriction;
    expect(r).toBeDefined();
    expect(r.status).toBe("discharged");
    expect(r.dischargedBy).toBe("constant");
    // Origin traces back to the step that spawned it.
    expect(r.origin).toEqual({ kind: "rule", stepId: node.id });
  });

  it("rejects dividing by a decidable zero", () => {
    const { eqn, d } = xEquals3();
    const j = d.current;
    expect(divideBothSides.precondition(j, eqn.id, { divisor: int(0) })).toBe(false);
    expect(() => d.apply(divideBothSides, eqn.id, { divisor: int(0) })).toThrow(
      RulePreconditionViolation,
    );
  });

  it("cancelling 2/2 folds to 1 and discharges 2 ≠ 0 on the spot", () => {
    const a = int(2);
    const b = int(2);
    const f = fraction([a], [b]);
    const eqn = equation(f, int(1));
    const d = new Derivation(eqn);
    d.apply(multiplicativeCancellation, f.id, { numTermId: a.id, denTermId: b.id });
    expect(eq(d.current.equation.lhs, int(1))).toBe(true);
    const r = d.current.assumptions[0] as Restriction;
    expect(r.kind).toBe("restriction");
    expect(r.status).toBe("discharged");
    expect(r.dischargedBy).toBe("constant");
  });

  it("pin discharges a restriction; unpin reactivates it", () => {
    const { eqn, d } = xEquals3();
    d.apply(divideBothSides, eqn.id, { divisor: variable("x") });
    const active = () => d.current.assumptions.find((a) => a.kind === "restriction") as Restriction;
    expect(active().status).toBe("active");

    d.pinVariable("x", Rational.of(2));
    expect(active().status).toBe("discharged");
    expect(active().dischargedBy).toBe("pins");

    d.unpinVariable("x");
    expect(active().status).toBe("active");
    expect(active().dischargedBy).toBeUndefined();
  });

  it("conflict, direction 1: pinning x = 0 makes dividing by x impossible", () => {
    const { eqn, d } = xEquals3();
    d.pinVariable("x", Rational.zero);
    expect(divideBothSides.precondition(d.current, eqn.id, { divisor: variable("x") })).toBe(false);
    expect(() => d.apply(divideBothSides, eqn.id, { divisor: variable("x") })).toThrow(
      RulePreconditionViolation,
    );
    // Same for cancellation of a pinned-zero factor.
    const x1 = variable("x");
    const x2 = variable("x");
    const f = fraction([x1], [x2]);
    const eqn2 = equation(f, int(1));
    const d2 = new Derivation(eqn2);
    d2.pinVariable("x", Rational.zero);
    expect(() =>
      d2.apply(multiplicativeCancellation, f.id, { numTermId: x1.id, denTermId: x2.id }),
    ).toThrow(RulePreconditionViolation);
  });

  it("conflict, direction 2: an existing Restriction x ≠ 0 blocks pinning x = 0", () => {
    const { eqn, d } = xEquals3();
    d.apply(divideBothSides, eqn.id, { divisor: variable("x") });
    const before = d.currentNode;
    expect(() => d.pinVariable("x", Rational.zero)).toThrow(AssumptionConflict);
    expect(d.currentNode).toBe(before); // rejected pin leaves no node
    // A compatible pin is fine.
    d.pinVariable("x", Rational.of(5));
  });

  it("guards the pin API: no double pins, no unpinning ghosts or case-split pins", () => {
    const { eqn, d } = xEquals3();
    d.pinVariable("x", Rational.of(1));
    expect(() => d.pinVariable("x", Rational.of(2))).toThrow(AssumptionConflict);
    expect(() => d.unpinVariable("y")).toThrow();

    const d2 = new Derivation(eqn);
    const { pinned } = d2.caseSplit(divideBothSides, eqn.id, { divisor: variable("x") });
    d2.goto(pinned.id);
    expect(() => d2.unpinVariable("x")).toThrow(AssumptionConflict);
  });

  it("case split on an already-pinned variable is vacuous and rejected", () => {
    const { eqn, d } = xEquals3();
    d.pinVariable("x", Rational.of(1));
    expect(() => d.caseSplit(divideBothSides, eqn.id, { divisor: variable("x") })).toThrow(
      AssumptionConflict,
    );
  });

  it("checkSolution without Extensions checks the current equation", () => {
    const { d } = xEquals3();
    expect(d.checkSolution(envOf([["x", 3]])).verdict).toBe("verified");
    expect(d.checkSolution(envOf([["x", 4]])).verdict).toBe("extraneous");
  });
});
