import type {
  EvidenceRef,
  OrchardVerificationData,
  ProofStatus,
  RepositoryId,
} from "../data/model";

const statusLabels: Record<ProofStatus, string> = {
  proved: "Proved in Rocq",
  checked: "Checked artifact",
  implemented: "Implemented",
  assumption: "Explicit hypothesis",
  boundary: "External boundary",
  wip: "Work in progress",
};

function EvidenceAnchor({
  evidence,
  repoName,
}: {
  evidence: EvidenceRef;
  repoName: string;
}) {
  const content = (
    <>
      <span className="evidence-chip__repo">{repoName}</span>
      <span className="evidence-chip__label">{evidence.label}</span>
      {evidence.anchor?.symbol ? (
        <code className="evidence-chip__symbol">{evidence.anchor.symbol}</code>
      ) : null}
      {evidence.publication === "pending" ? (
        <span className="evidence-chip__pending">publishes with branch</span>
      ) : null}
    </>
  );

  if (!evidence.url) {
    return (
      <span className="evidence-chip evidence-chip--static" title={evidence.description}>
        {content}
      </span>
    );
  }

  return (
    <a
      className="evidence-chip"
      href={evidence.url}
      target="_blank"
      rel="noopener noreferrer"
      title={evidence.description}
    >
      {content}
      <span aria-hidden="true">↗</span>
    </a>
  );
}

export function EvidencePanel({
  data,
  evidenceIds,
  heading = "Evidence",
}: {
  data: OrchardVerificationData;
  evidenceIds: readonly string[];
  heading?: string;
}) {
  const evidenceById = new Map(data.evidence.map((item) => [item.id, item]));
  const repoById = new Map(data.repositories.map((repo) => [repo.id, repo]));
  const items = evidenceIds
    .map((id) => evidenceById.get(id))
    .filter((item): item is EvidenceRef => Boolean(item));

  if (items.length === 0) return null;

  return (
    <section className="evidence-panel" aria-labelledby="stage-evidence-title">
      <h3 id="stage-evidence-title">{heading}</h3>
      <div className="evidence-list">
        {items.map((item) => (
          <EvidenceAnchor
            evidence={item}
            key={item.id}
            repoName={repoById.get(item.repoId)?.shortName ?? item.repoId}
          />
        ))}
      </div>
    </section>
  );
}

export function StatusBadge({ status }: { status: ProofStatus }) {
  return (
    <span className={`status-badge status-badge--${status}`}>
      <span className="status-badge__seed" aria-hidden="true" />
      {statusLabels[status]}
    </span>
  );
}

export function RepositoryBadges({
  data,
  repoIds,
}: {
  data: OrchardVerificationData;
  repoIds: readonly RepositoryId[];
}) {
  const repositories = new Map(data.repositories.map((repo) => [repo.id, repo]));
  return (
    <div className="repository-badges" aria-label="Repositories involved">
      {repoIds.map((repoId) => {
        const repo = repositories.get(repoId);
        return (
          <span
            className="repository-badge"
            key={repoId}
            style={{ "--repo-color": repo?.color } as React.CSSProperties}
          >
            {repo?.shortName ?? repoId}
          </span>
        );
      })}
    </div>
  );
}

export { statusLabels };
