export const CIRCUIT_EXPLORER_SCHEMA =
  "garden.orchard.circuit-highlevel.v1" as const;

export type CircuitExplorerLevel = "flow" | "component" | "detail";
export type CircuitExplorerMode = "aggregate" | "exact";
export type CircuitSourceConfidence = "exact" | "mapped" | "ambiguous" | "unresolved";

export type CircuitItemKind =
  | "input"
  | "component"
  | "check"
  | "output"
  | "region"
  | "region-occurrence"
  | "gate"
  | "lookup"
  | "constraint"
  | "operation";

export interface CircuitPoint {
  readonly x: number;
  readonly y: number;
}

export interface CircuitMetric {
  readonly id: string;
  readonly label: string;
  readonly value: string;
  readonly detail?: string;
}

export interface CircuitSource {
  readonly id: string;
  readonly label: string;
  readonly path: string;
  readonly symbol?: string;
  readonly line?: number;
  readonly url?: string;
  readonly repository?: string;
  readonly revision?: string;
  readonly confidence: CircuitSourceConfidence;
  readonly candidates: readonly CircuitSourceCandidate[];
}

export interface CircuitSourceCandidate {
  readonly label: string;
  readonly path: string;
  readonly symbol?: string;
  readonly line?: number;
  readonly confidence?: string;
}

export interface CircuitSourceResolutionCandidate {
  readonly sourceId: string;
  readonly confidence: CircuitSourceConfidence;
  readonly reason?: string;
}

export interface CircuitFlowNode {
  readonly id: string;
  readonly kind: "input" | "component" | "check" | "output";
  readonly title: string;
  readonly shortTitle: string;
  readonly summary: string;
  readonly componentId?: string;
  readonly regionIds: readonly string[];
  readonly gateIds: readonly string[];
  readonly lookupIds: readonly string[];
  readonly operationIds: readonly string[];
  readonly instanceRowIds: readonly string[];
  readonly sourceIds: readonly string[];
  readonly proofNodeIds: readonly string[];
  readonly position?: CircuitPoint;
  readonly metrics: readonly CircuitMetric[];
  readonly tags: readonly string[];
}

export interface CircuitFlowEdge {
  readonly id: string;
  readonly from: string;
  readonly to: string;
  readonly label?: string;
  readonly kind: "data" | "constraint" | "public";
}

export interface CircuitComponent {
  readonly id: string;
  readonly title: string;
  readonly shortTitle: string;
  readonly summary: string;
  readonly detail: string;
  readonly regionIds: readonly string[];
  readonly gateIds: readonly string[];
  readonly lookupIds: readonly string[];
  readonly operationIds: readonly string[];
  readonly instanceRowIds: readonly string[];
  readonly sourceIds: readonly string[];
  readonly sourceConfidence?: CircuitSourceConfidence;
  readonly sourceCandidateIds: readonly string[];
  readonly sourceCandidates: readonly CircuitSourceResolutionCandidate[];
  readonly proofNodeIds: readonly string[];
  readonly metrics: readonly CircuitMetric[];
  readonly tags: readonly string[];
}

export interface CircuitRegionGroup {
  readonly id: string;
  readonly componentId: string;
  readonly title: string;
  readonly semanticId?: string;
  readonly summary: string;
  readonly namespacePath: readonly string[];
  readonly occurrenceIds: readonly string[];
  readonly gateIds: readonly string[];
  readonly sourceIds: readonly string[];
  readonly sourceConfidence?: CircuitSourceConfidence;
  readonly sourceCandidateIds: readonly string[];
  readonly sourceCandidates: readonly CircuitSourceResolutionCandidate[];
  readonly metrics: readonly CircuitMetric[];
  readonly count: number;
  readonly eventCount: number;
  readonly selectorCount: number;
  readonly copyCount: number;
  readonly rowStart?: number;
  readonly rowEnd?: number;
  readonly searchTerms: readonly string[];
}

export interface CircuitRegionOccurrence {
  readonly id: string;
  readonly groupId: string;
  readonly componentId: string;
  readonly title: string;
  readonly semanticId?: string;
  readonly index: number;
  readonly namespacePath: readonly string[];
  readonly sourceIds: readonly string[];
  readonly sourceConfidence?: CircuitSourceConfidence;
  readonly sourceCandidateIds: readonly string[];
  readonly sourceCandidates: readonly CircuitSourceResolutionCandidate[];
  readonly operationIds: readonly string[];
  readonly metrics: readonly CircuitMetric[];
  readonly eventCount: number;
  readonly selectorCount: number;
  readonly copyCount: number;
  readonly rowStart?: number;
  readonly rowEnd?: number;
  readonly searchTerms: readonly string[];
}

export interface CircuitNamespace {
  readonly id: string;
  readonly title: string;
  readonly parentId?: string;
  readonly componentId?: string;
  readonly childIds: readonly string[];
  readonly regionIds: readonly string[];
  readonly path: readonly string[];
  readonly sourceIds: readonly string[];
}

export interface CircuitCell {
  readonly id: string;
  readonly kind: "advice" | "fixed" | "instance" | "lookup" | "unknown";
  readonly column?: string;
  readonly regionId?: string;
  readonly relativeOffset?: number;
  readonly absoluteRow?: number;
  readonly label: string;
}

export interface CircuitRegionOperation {
  readonly id: string;
  readonly componentId?: string;
  readonly occurrenceId?: string;
  readonly regionId?: string;
  readonly kind:
    | "enable-selector"
    | "assign-fixed"
    | "copy"
    | "constrain-constant"
    | "constrain-instance"
    | "init-lookup-tables"
    | "other";
  readonly title: string;
  readonly annotation?: string;
  readonly selectorId?: string;
  readonly selectorName?: string;
  readonly relativeOffset?: number;
  readonly absoluteRow?: number;
  readonly cells: readonly CircuitCell[];
  readonly value?: string;
  readonly lookupEntries: readonly CircuitLookupTableEntry[];
  readonly sourceIds: readonly string[];
  readonly sourceConfidence?: CircuitSourceConfidence;
  readonly sourceCandidateIds: readonly string[];
  readonly sourceCandidates: readonly CircuitSourceResolutionCandidate[];
}

export interface CircuitLookupTableEntry {
  readonly id: string;
  readonly column?: string;
  readonly columnName?: string;
  readonly annotation?: string;
  readonly valueCount?: number;
  readonly defaultValue?: string;
}

export interface CircuitConstraint {
  readonly id: string;
  readonly gateId: string;
  readonly title: string;
  readonly expression: string;
  readonly expressionAst?: unknown;
  readonly columns: readonly string[];
  readonly rotations: readonly number[];
  readonly sourceIds: readonly string[];
  readonly sourceConfidence?: CircuitSourceConfidence;
  readonly sourceCandidateIds: readonly string[];
  readonly sourceCandidates: readonly CircuitSourceResolutionCandidate[];
}

export interface CircuitGate {
  readonly id: string;
  readonly componentId?: string;
  readonly componentIds: readonly string[];
  readonly title: string;
  readonly summary: string;
  readonly selector?: string;
  readonly constraintIds: readonly string[];
  readonly regionIds: readonly string[];
  readonly sourceIds: readonly string[];
  readonly sourceConfidence?: CircuitSourceConfidence;
  readonly sourceCandidateIds: readonly string[];
  readonly sourceCandidates: readonly CircuitSourceResolutionCandidate[];
  readonly metrics: readonly CircuitMetric[];
  readonly searchTerms: readonly string[];
}

export interface CircuitLookup {
  readonly id: string;
  readonly componentId?: string;
  readonly componentIds: readonly string[];
  readonly title: string;
  readonly summary: string;
  readonly pairCount: number;
  readonly pairs: readonly CircuitLookupPair[];
  readonly selectorIds: readonly string[];
  readonly tableIds: readonly string[];
  readonly regionIds: readonly string[];
  readonly sourceIds: readonly string[];
  readonly sourceConfidence?: CircuitSourceConfidence;
  readonly sourceCandidateIds: readonly string[];
  readonly sourceCandidates: readonly CircuitSourceResolutionCandidate[];
  readonly metrics: readonly CircuitMetric[];
  readonly searchTerms: readonly string[];
}

export interface CircuitLookupPair {
  readonly id: string;
  readonly inputExpression: string;
  readonly inputAst?: unknown;
  readonly tableId?: string;
  readonly tableName?: string;
}

export interface CircuitMetadata {
  readonly title: string;
  readonly description: string;
  readonly asOf: string;
  readonly placement: string;
  readonly representations: Readonly<Record<string, string>>;
  readonly repositoryRefs: Readonly<Record<string, string>>;
  readonly metrics: readonly CircuitMetric[];
}

export interface CircuitDiagnostic {
  readonly id: string;
  readonly severity: "info" | "warning" | "error";
  readonly message: string;
  readonly itemId?: string;
  readonly itemIds: readonly string[];
}

export interface CircuitExplorerData {
  readonly schema: typeof CIRCUIT_EXPLORER_SCHEMA;
  readonly metadata: CircuitMetadata;
  readonly flow: {
    readonly nodes: readonly CircuitFlowNode[];
    readonly edges: readonly CircuitFlowEdge[];
    readonly bounds: { readonly width: number; readonly height: number };
  };
  readonly synthesis: {
    readonly components: readonly CircuitComponent[];
    readonly namespaces: readonly CircuitNamespace[];
    readonly regions: readonly CircuitRegionGroup[];
    readonly occurrences: readonly CircuitRegionOccurrence[];
    readonly operations: readonly CircuitRegionOperation[];
  };
  readonly configure: {
    readonly gates: readonly CircuitGate[];
    readonly constraints: readonly CircuitConstraint[];
    readonly lookups: readonly CircuitLookup[];
  };
  readonly sources: readonly CircuitSource[];
  readonly diagnostics: readonly CircuitDiagnostic[];
}

export interface CircuitExplorerRoute {
  readonly level: CircuitExplorerLevel;
  readonly itemId: string | null;
  readonly mode: CircuitExplorerMode;
  readonly query: string;
}

export type InspectableCircuitItem =
  | CircuitFlowNode
  | CircuitComponent
  | CircuitRegionGroup
  | CircuitRegionOccurrence
  | CircuitGate
  | CircuitLookup
  | CircuitConstraint
  | CircuitRegionOperation;
