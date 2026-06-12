import { readdirSync, readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";

/**
 * @wyrm/core must run in pure Node: zero DOM/browser usage and no dependency
 * on @wyrm/ui, ever. The tsconfig (`lib: ES2022`, `types: []`) catches most
 * of this at typecheck time; this test backstops it mechanically in CI.
 */
const FORBIDDEN: readonly { pattern: RegExp; why: string }[] = [
  { pattern: /@wyrm\/ui/, why: "core must never import @wyrm/ui" },
  { pattern: /\b(document|window|navigator|localStorage|HTMLElement|SVGElement)\b/, why: "browser global" },
  { pattern: /from\s+["'](react|vue|svelte)/, why: "UI framework import" },
];

function tsFilesUnder(dir: string): string[] {
  return readdirSync(dir, { withFileTypes: true, recursive: true })
    .filter((e) => e.isFile() && e.name.endsWith(".ts"))
    .map((e) => join(e.parentPath, e.name));
}

describe("core/ui boundary", () => {
  const srcDir = join(dirname(fileURLToPath(import.meta.url)), "..", "src");

  it("src contains no browser or UI-package references", () => {
    const files = tsFilesUnder(srcDir);
    expect(files.length).toBeGreaterThan(0);
    for (const file of files) {
      const content = readFileSync(file, "utf8");
      for (const { pattern, why } of FORBIDDEN) {
        expect(pattern.test(content), `${file}: ${why} (${pattern})`).toBe(false);
      }
    }
  });
});
