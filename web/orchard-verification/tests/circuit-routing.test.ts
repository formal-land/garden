import { describe, expect, it } from "vitest";

import {
  circuitExplorerHref,
  circuitExplorerRouteHash,
  circuitExplorerTargetRoute,
  defaultCircuitExplorerRoute,
} from "../src/circuit/routing";

describe("Circuit Explorer routing", () => {
  it("keeps the empty flow route canonical", () => {
    expect(circuitExplorerRouteHash(defaultCircuitExplorerRoute())).toBe("");
  });

  it("links components directly and nested operations through their owner", () => {
    expect(circuitExplorerHref({
      id: "component:merkle-path",
      kind: "component",
    })).toBe(
      "./circuit.html#level=component&item=component%3Amerkle-path",
    );

    expect(circuitExplorerHref({
      id: "region:2/op:0",
      kind: "operation",
      ownerId: "region:2",
      componentId: "component:private-inputs",
    })).toBe(
      "./circuit.html#level=detail&item=region%3A2&focus=region%3A2%2Fop%3A0",
    );
  });

  it("focuses constraints inside their owning gate", () => {
    expect(circuitExplorerTargetRoute({
      id: "constraint:gate-0:0",
      kind: "constraint",
      ownerId: "gate:0",
    })).toEqual({
      level: "detail",
      itemId: "gate:0",
      query: "",
      focusId: "constraint:gate-0:0",
    });
  });
});
