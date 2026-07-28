export const CIRCUIT_GRID_SCHEMA = "garden.halo2.circuit-grid.v1" as const;

export type CircuitGridStage =
  | "pre-selector-compression"
  | "post-selector-compression"
  | "compiled"
  | string;

export type CircuitGridColumnKind = "instance" | "advice" | "fixed";

export type CircuitGridEventKind =
  | "assign-fixed"
  | "enable-selector"
  | "copy"
  | "fill"
  | "constrain-constant"
  | "constrain-instance"
  | "advice-reference"
  | "region-start"
  | "other";

export type CircuitGridTargetKind =
  | "component"
  | "region"
  | "operation"
  | "gate"
  | "lookup"
  | "constraint"
  | "other";

export interface CircuitGridCircuitMetadata {
  readonly id: string;
  readonly name: string;
  readonly version: string;
  readonly field: string;
  readonly k: number;
  readonly rowCount: number;
  readonly floorPlanner: string;
  readonly stage: CircuitGridStage;
}

export interface CircuitGridCapabilities {
  readonly adviceAssignments: string;
  readonly witnessValues: string;
  readonly selectors: string;
  readonly permutation: string;
}

export interface CircuitGridInput {
  readonly id: string;
  readonly path: string;
  readonly sha256?: string;
}

export interface CircuitGridMetadata {
  readonly circuit: CircuitGridCircuitMetadata;
  readonly capabilities: CircuitGridCapabilities;
  readonly inputs: readonly CircuitGridInput[];
  readonly parity: Readonly<Record<string, string>>;
  readonly repositoryRefs: Readonly<Record<string, string>>;
}

export interface CircuitGridTarget {
  readonly id: string;
  readonly kind: CircuitGridTargetKind;
  readonly title: string;
  readonly href: string;
}

export interface CircuitGridColumn {
  readonly id: string;
  readonly kind: CircuitGridColumnKind;
  readonly index: number;
  readonly name: string;
  readonly role?: string;
  readonly circuitTarget?: CircuitGridTarget;
}

export interface CircuitGridSelector {
  readonly id: string;
  readonly index: number;
  readonly name: string;
  readonly gateIds: readonly string[];
  readonly lookupIds: readonly string[];
  readonly circuitTarget?: CircuitGridTarget;
}

export interface CircuitGridRegion {
  readonly id: string;
  readonly regionIndex: number;
  readonly startRow: number;
  readonly endRow?: number;
  readonly name: string;
  readonly namespace: readonly string[];
  readonly componentId?: string;
  readonly selectorIds: readonly string[];
  readonly gateIds: readonly string[];
  readonly lookupIds: readonly string[];
  readonly operationIds: readonly string[];
  readonly circuitTarget?: CircuitGridTarget;
}

export interface CircuitGridEndpoint {
  readonly columnId: string;
  readonly row: number;
}

export interface CircuitGridEvent {
  readonly id: string;
  readonly kind: CircuitGridEventKind;
  readonly sourceIndex?: number;
  readonly sourceTag?: string;
  readonly row?: number;
  readonly columnId?: string;
  readonly selectorId?: string;
  readonly annotation?: string;
  readonly value?: string;
  readonly fromRow?: number;
  readonly toRow?: number;
  readonly endpoints: readonly CircuitGridEndpoint[];
  readonly peerEventIds: readonly string[];
  readonly regionId?: string;
  readonly namespace: readonly string[];
  readonly gateIds: readonly string[];
  readonly lookupIds: readonly string[];
  readonly operationIds: readonly string[];
  readonly circuitTarget?: CircuitGridTarget;
}

export interface CircuitGridSparseRow {
  readonly row: number;
  readonly eventIds: readonly string[];
  readonly regionIds: readonly string[];
  readonly selectorIds: readonly string[];
  readonly columnIds: readonly string[];
}

export interface CircuitGridSummary {
  readonly columnCount: number;
  readonly selectorCount: number;
  readonly regionCount: number;
  readonly eventCount: number;
  readonly populatedRowCount: number;
  readonly counts: Readonly<Record<string, number>>;
}

export interface CircuitGridData {
  readonly schema: typeof CIRCUIT_GRID_SCHEMA;
  readonly metadata: CircuitGridMetadata;
  readonly columns: readonly CircuitGridColumn[];
  readonly selectors: readonly CircuitGridSelector[];
  readonly regions: readonly CircuitGridRegion[];
  readonly events: readonly CircuitGridEvent[];
  readonly rows: readonly CircuitGridSparseRow[];
  readonly targets: readonly CircuitGridTarget[];
  readonly summary: CircuitGridSummary;
}

export type CircuitGridTrack =
  | {
      readonly id: string;
      readonly kind: CircuitGridColumnKind;
      readonly label: string;
      readonly description: string;
      readonly column: CircuitGridColumn;
    }
  | {
      readonly id: string;
      readonly kind: "selector";
      readonly label: string;
      readonly description: string;
      readonly selector: CircuitGridSelector;
    }
  | {
      readonly id: "selectors:collapsed";
      readonly kind: "selectors";
      readonly label: "Q";
      readonly description: string;
    };

export interface CircuitGridMark {
  readonly id: string;
  readonly kind: CircuitGridEventKind;
  readonly label: string;
  readonly event: CircuitGridEvent;
  readonly selector?: CircuitGridSelector;
  readonly peer?: CircuitGridEndpoint;
  readonly fromRange?: boolean;
}

export interface CircuitGridCellProjection {
  readonly row: number;
  readonly track: CircuitGridTrack;
  readonly marks: readonly CircuitGridMark[];
  readonly regions: readonly CircuitGridRegion[];
  readonly targets: readonly CircuitGridTarget[];
}

export interface CircuitGridSearchResult {
  readonly id: string;
  readonly kind: "row" | "region" | "component" | "selector";
  readonly title: string;
  readonly detail: string;
  readonly row: number;
  readonly columnId?: string;
}

export interface CircuitGridSelection {
  readonly row: number;
  readonly columnId: string;
}
