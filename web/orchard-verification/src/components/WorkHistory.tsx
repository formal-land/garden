import type {
  OrchardVerificationData,
  WorkReference,
  WorkUnit,
} from "../data/model";

function formatDate(value: string): string {
  return new Intl.DateTimeFormat("en-GB", {
    day: "numeric",
    month: "short",
    year: "numeric",
    timeZone: "UTC",
  }).format(new Date(`${value}T00:00:00Z`));
}

function formatRange(workUnit: WorkUnit): string {
  if (workUnit.startDate === workUnit.endDate) {
    return formatDate(workUnit.endDate);
  }
  return `${formatDate(workUnit.startDate)}–${formatDate(workUnit.endDate)}`;
}

function referenceLabel(reference: WorkReference): string {
  if (reference.kind === "migrated-pr") {
    return `Migrated PR #${reference.number}`;
  }
  if (reference.kind === "public-pr") {
    return `PR #${reference.number}`;
  }
  return `Commit ${reference.commitRef?.slice(0, 7) ?? ""}`.trim();
}

function ReferenceLink({ reference }: { reference: WorkReference }) {
  return (
    <a
      className="work-reference"
      href={reference.url}
      target="_blank"
      rel="noopener noreferrer"
      title={reference.description}
    >
      <span>
        <strong>{referenceLabel(reference)}</strong>
        <small>{reference.title}</small>
      </span>
      <span aria-hidden="true">↗</span>
    </a>
  );
}

function WorkUnitCard({
  data,
  workUnit,
  expandable = true,
}: {
  data: OrchardVerificationData;
  workUnit: WorkUnit;
  expandable?: boolean;
}) {
  const contributorById = new Map(
    data.development.contributors.map((contributor) => [contributor.id, contributor]),
  );
  const referenceById = new Map(
    data.development.references.map((reference) => [reference.id, reference]),
  );
  const contributors = workUnit.contributorIds
    .map((id) => contributorById.get(id))
    .filter((contributor) => contributor !== undefined);
  const references = workUnit.referenceIds
    .map((id) => referenceById.get(id))
    .filter((reference) => reference !== undefined);

  return (
    <article
      className={`work-unit-card work-unit-card--${workUnit.scope}`}
      data-work-unit-id={workUnit.id}
    >
      <header>
        <div>
          <p className="work-unit-card__meta">
            {formatRange(workUnit)} · {workUnit.status === "completed" ? "Completed" : "In progress"}
          </p>
          <h4>{workUnit.title}</h4>
        </div>
        <span className="work-unit-card__count">
          {references.length} {references.length === 1 ? "change" : "changes"}
        </span>
      </header>
      <p>{workUnit.summary}</p>
      <p className="work-unit-card__contributors">
        <span>Contributors</span>
        {contributors.map((contributor, index) => (
          <span key={contributor.id}>
            {index > 0 ? ", " : " "}
            <a href={contributor.url} target="_blank" rel="noopener noreferrer">
              {contributor.name} <small>{contributor.handle}</small>
            </a>
          </span>
        ))}
      </p>
      {references.length ? (
        expandable ? (
          <details className="work-unit-card__references">
            <summary>Pull requests and commits ({references.length})</summary>
            <div>
              {references.map((reference) => (
                <ReferenceLink reference={reference} key={reference.id} />
              ))}
            </div>
          </details>
        ) : (
          <div className="work-unit-card__references-list">
            {references.map((reference) => (
              <ReferenceLink reference={reference} key={reference.id} />
            ))}
          </div>
        )
      ) : null}
    </article>
  );
}

export function WorkUnitPanel({
  data,
  workUnitIds,
  heading = "Work delivered",
  expandable = true,
}: {
  data: OrchardVerificationData;
  workUnitIds: readonly string[];
  heading?: string;
  expandable?: boolean;
}) {
  const workUnitById = new Map(
    data.development.workUnits.map((workUnit) => [workUnit.id, workUnit]),
  );
  const workUnits = workUnitIds
    .map((id) => workUnitById.get(id))
    .filter((workUnit) => workUnit !== undefined);

  if (!workUnits.length) return null;

  return (
    <section className="work-unit-panel" aria-label={heading}>
      <div className="work-unit-panel__heading">
        <h3>{heading}</h3>
        <span>{workUnits.length} {workUnits.length === 1 ? "unit" : "units"}</span>
      </div>
      <div className="work-unit-panel__grid">
        {workUnits.map((workUnit) => (
          <WorkUnitCard
            data={data}
            expandable={expandable}
            key={workUnit.id}
            workUnit={workUnit}
          />
        ))}
      </div>
    </section>
  );
}

export function WorkUnitChips({
  data,
  workUnitIds,
}: {
  data: OrchardVerificationData;
  workUnitIds: readonly string[];
}) {
  const workUnitById = new Map(
    data.development.workUnits.map((workUnit) => [workUnit.id, workUnit]),
  );
  return (
    <div
      className="work-unit-chips"
      role="list"
      aria-label="Development work units"
    >
      {workUnitIds.map((id) => {
        const workUnit = workUnitById.get(id);
        return workUnit ? (
          <span key={id} role="listitem">{workUnit.shortTitle}</span>
        ) : null;
      })}
    </div>
  );
}

export function DevelopmentSummary({ data }: { data: OrchardVerificationData }) {
  const referenceById = new Map(
    data.development.references.map((reference) => [reference.id, reference]),
  );
  const verificationPullRequest = referenceById.get(
    data.development.verificationPullRequestId,
  );
  const websitePullRequest = referenceById.get(
    data.development.websitePullRequestId,
  );
  const publicationUnits = data.development.workUnits.filter(
    ({ scope }) => scope === "publication",
  );

  return (
    <section className="development-summary" aria-labelledby="development-summary-title">
      <header className="development-summary__heading">
        <div>
          <p className="eyebrow">Public development record · through {formatDate(data.development.asOf)}</p>
          <h2 id="development-summary-title">From proof work to a public, inspectable artifact</h2>
        </div>
        <p>
          Historical private PR numbers are retained as provenance labels. They
          open the preserved public merge or squash commit, so every link stays
          inside formal-land/garden.
        </p>
      </header>
      <div className="development-summary__pulls">
        {verificationPullRequest ? (
          <a href={verificationPullRequest.url} target="_blank" rel="noopener noreferrer">
            <span>Merged verification</span>
            <strong>PR #88 · {verificationPullRequest.title}</strong>
            <small>98 commits · merged 27 Jul 2026</small>
          </a>
        ) : null}
        {websitePullRequest ? (
          <a href={websitePullRequest.url} target="_blank" rel="noopener noreferrer">
            <span>Current public website work</span>
            <strong>PR #89 · {websitePullRequest.title}</strong>
            <small>Through commit {websitePullRequest.commitRef?.slice(0, 7)} · 28 Jul 2026</small>
          </a>
        ) : null}
      </div>
      <div className="development-summary__timeline">
        {publicationUnits.map((workUnit) => (
          <WorkUnitCard data={data} key={workUnit.id} workUnit={workUnit} />
        ))}
      </div>
    </section>
  );
}
