/**
 * Canonical content model shared by the journey and atlas views.
 *
 * The model deliberately keeps proof status, repository provenance, and URL
 * publication status separate. A locally checked theorem can therefore be
 * marked `proved` while its Garden source link remains `pending` publication.
 */

export type RepositoryId = "garden" | "halo2" | "orchard" | "protocol";

export type PublicationStatus = "public" | "pending" | "local";

export type ProofStatus =
  | "proved"
  | "checked"
  | "implemented"
  | "assumption"
  | "boundary"
  | "wip";

export type WorkTrack =
  | "capture"
  | "parity"
  | "semantics"
  | "foundations"
  | "gadgets"
  | "action"
  | "balance"
  | "engineering"
  | "trust";

export type EvidenceKind =
  | "commit"
  | "source"
  | "theorem"
  | "documentation"
  | "artifact"
  | "report"
  | "specification";

export interface RepositoryRevision {
  readonly ref: string;
  readonly shortRef: string;
  readonly label: string;
  readonly date: string;
  readonly publication: PublicationStatus;
  readonly url?: string;
}

export interface Repository {
  readonly id: RepositoryId;
  readonly name: string;
  readonly shortName: string;
  readonly description: string;
  readonly color: string;
  readonly url: string;
  readonly revisions: readonly RepositoryRevision[];
}

export interface SourceAnchor {
  readonly path: string;
  readonly symbol?: string;
  readonly line?: number;
}

export interface EvidenceRef {
  readonly id: string;
  readonly repoId: RepositoryId;
  readonly revision?: string;
  readonly kind: EvidenceKind;
  readonly label: string;
  readonly description: string;
  readonly date?: string;
  readonly publication: PublicationStatus;
  readonly anchor?: SourceAnchor;
  readonly url?: string;
  /** A public fallback, usually a protocol section, when the primary URL is pending. */
  readonly publicFallbackUrl?: string;
  readonly status: ProofStatus;
  readonly tags?: readonly string[];
}

export interface AtlasPoint {
  readonly x: number;
  readonly y: number;
}

export interface AtlasBounds extends AtlasPoint {
  readonly width: number;
  readonly height: number;
}

export interface Metric {
  readonly label: string;
  readonly value: string;
  readonly detail?: string;
}

export interface ProofNode {
  readonly id: string;
  readonly clusterId: string;
  readonly title: string;
  readonly shortTitle: string;
  readonly summary: string;
  readonly detail: string;
  readonly status: ProofStatus;
  readonly track: WorkTrack;
  readonly repoIds: readonly RepositoryId[];
  readonly evidenceIds: readonly string[];
  readonly stageIds: readonly string[];
  readonly position: AtlasPoint;
  readonly established: readonly string[];
  readonly carried: readonly string[];
  readonly metrics?: readonly Metric[];
  readonly tags: readonly string[];
}

export interface ProofCluster {
  readonly id: string;
  readonly title: string;
  readonly shortTitle: string;
  readonly summary: string;
  readonly status: ProofStatus;
  readonly track: WorkTrack;
  readonly repoIds: readonly RepositoryId[];
  readonly bounds: AtlasBounds;
  readonly nodeIds: readonly string[];
  readonly collapsedSummary: string;
}

export type FormalRelation =
  | "proves"
  | "entails"
  | "depends-on"
  | "composes"
  | "limits";

export type ProvenanceRelation =
  | "serializes"
  | "matches"
  | "models"
  | "derives-from"
  | "validates"
  | "repairs";

interface EdgeBase {
  readonly id: string;
  readonly from: string;
  readonly to: string;
  readonly label: string;
  readonly status: ProofStatus;
  readonly evidenceIds: readonly string[];
  readonly stageIds: readonly string[];
}

export interface FormalProofEdge extends EdgeBase {
  readonly family: "formal";
  readonly relation: FormalRelation;
}

export interface ProvenanceProofEdge extends EdgeBase {
  readonly family: "provenance";
  readonly relation: ProvenanceRelation;
}

export type ProofEdge = FormalProofEdge | ProvenanceProofEdge;

export interface JourneyStage {
  readonly id: string;
  readonly ordinal: number;
  readonly date: string;
  readonly eyebrow: string;
  readonly title: string;
  readonly purpose: string;
  readonly claim: string;
  readonly narrative: string;
  readonly status: ProofStatus;
  readonly tracks: readonly WorkTrack[];
  readonly repoIds: readonly RepositoryId[];
  readonly nodeIds: readonly string[];
  readonly evidenceIds: readonly string[];
  readonly established: readonly string[];
  readonly carried: readonly string[];
}

export interface EvidenceSnapshot {
  readonly id: string;
  readonly title: string;
  readonly asOf: string;
  readonly description: string;
  readonly repositoryRefs: Readonly<Record<"garden" | "halo2" | "orchard", string>>;
  readonly caveat: string;
}

export interface FilterOption<T extends string> {
  readonly id: T;
  readonly label: string;
  readonly description: string;
}

export interface OrchardVerificationData {
  readonly snapshot: EvidenceSnapshot;
  readonly repositories: readonly Repository[];
  readonly evidence: readonly EvidenceRef[];
  readonly clusters: readonly ProofCluster[];
  readonly nodes: readonly ProofNode[];
  readonly edges: readonly ProofEdge[];
  readonly stages: readonly JourneyStage[];
  readonly filters: {
    readonly repositories: readonly FilterOption<RepositoryId>[];
    readonly statuses: readonly FilterOption<ProofStatus>[];
    readonly tracks: readonly FilterOption<WorkTrack>[];
  };
}
