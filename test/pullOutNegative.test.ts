import { describe, expect, it } from "vitest";
import {
  applyRule,
  equation,
  evalExpr,
  int,
  mkJudgment,
  neg,
  product,
  pullOutNegative,
  Rational,
  variable,
} from "../src/index.js";

describe("pull-out-negative", () => {
  it("pulls a single negative factor to the front, value preserved", () => {
    // (−20)·x → −(20·x)
    const t = product([int(-20), variable("x")]);
    const j = mkJudgment(equation(t, int(0)));
    expect(pullOutNegative.precondition(j, t.id, {})).toBe(true);
    const after = applyRule(j, pullOutNegative, t.id, {}).judgment.equation;
    expect(after.lhs.kind).toBe("neg"); // −(20·x), minus out front
    const at3 = new Map([["x", new Rational(3n)]]);
    expect(evalExpr(t, at3).asRational()?.equals(new Rational(-60n))).toBe(true);
    expect(evalExpr(after.lhs, at3).asRational()?.equals(new Rational(-60n))).toBe(true);

    // 20·(−y) → −(20·y) (the negative can be on the variable too)
    const u = product([int(20), neg(variable("y"))]);
    const ju = mkJudgment(equation(u, int(0)));
    expect(pullOutNegative.precondition(ju, u.id, {})).toBe(true);
    expect(applyRule(ju, pullOutNegative, u.id, {}).judgment.equation.lhs.kind).toBe("neg");
  });

  it("does not fire on a pure numeric product or a two-negative product", () => {
    const num = product([int(4), int(-8)]); // 4·(−8): combine-integer-factors handles it
    expect(pullOutNegative.precondition(mkJudgment(equation(num, int(0))), num.id, {})).toBe(false);
    const two = product([int(-2), neg(variable("y"))]); // (−2)(−y): cancel-negatives handles it
    expect(pullOutNegative.precondition(mkJudgment(equation(two, int(0))), two.id, {})).toBe(false);
  });
});
