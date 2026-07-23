import type { CircuitExplorerRoute, CircuitItemKind } from "./model";

export interface CircuitExplorerTarget {
  readonly id: string;
  readonly kind: CircuitItemKind;
  readonly ownerId?: string;
  readonly componentId?: string;
}

export function defaultCircuitExplorerRoute(): CircuitExplorerRoute {
  return { level: "flow", itemId: null, query: "", focusId: null };
}

export function circuitExplorerRouteHash(route: CircuitExplorerRoute): string {
  const parameters = new URLSearchParams();
  if (route.level !== "flow") parameters.set("level", route.level);
  if (route.itemId) parameters.set("item", route.itemId);
  if (route.query) parameters.set("q", route.query);
  if (route.focusId) parameters.set("focus", route.focusId);
  const value = parameters.toString();
  return value ? `#${value}` : "";
}

export function circuitExplorerTargetRoute(
  target: CircuitExplorerTarget,
): CircuitExplorerRoute {
  if (target.kind === "component") {
    return {
      level: "component",
      itemId: target.id,
      query: "",
      focusId: null,
    };
  }

  if (target.kind === "operation") {
    if (target.ownerId) {
      return {
        level: "detail",
        itemId: target.ownerId,
        query: "",
        focusId: target.id,
      };
    }
    if (target.componentId) {
      return {
        level: "component",
        itemId: target.componentId,
        query: "",
        focusId: target.id,
      };
    }
  }

  if (target.kind === "constraint" && target.ownerId) {
    return {
      level: "detail",
      itemId: target.ownerId,
      query: "",
      focusId: target.id,
    };
  }

  return {
    level:
      target.kind === "input" ||
      target.kind === "check" ||
      target.kind === "output"
        ? "flow"
        : "detail",
    itemId: target.id,
    query: "",
    focusId: null,
  };
}

export function circuitExplorerHref(
  target: CircuitExplorerTarget,
  page = "./circuit.html",
): string {
  return `${page}${circuitExplorerRouteHash(circuitExplorerTargetRoute(target))}`;
}
