import type {
  OrchardVerificationData,
  ProofNode,
  ProofStatus,
  RepositoryId,
  WorkTrack,
} from "./model";

export interface DataValidationIssue {
  readonly path: string;
  readonly message: string;
}

function duplicateValues(values: readonly string[]): string[] {
  const seen = new Set<string>();
  const duplicates = new Set<string>();
  for (const value of values) {
    if (seen.has(value)) duplicates.add(value);
    seen.add(value);
  }
  return [...duplicates];
}

function insideCluster(node: ProofNode, data: OrchardVerificationData): boolean {
  const cluster = data.clusters.find((candidate) => candidate.id === node.clusterId);
  if (!cluster) return false;
  return (
    node.position.x >= cluster.bounds.x &&
    node.position.x <= cluster.bounds.x + cluster.bounds.width &&
    node.position.y >= cluster.bounds.y &&
    node.position.y <= cluster.bounds.y + cluster.bounds.height
  );
}

/**
 * Runtime validation used by tests and CI. It intentionally validates the
 * evidence graph as content, rather than relying only on TypeScript's shape
 * checks, so misspelled IDs and accidental WIP-to-established dependencies
 * fail loudly.
 */
export function validateOrchardVerificationData(
  data: OrchardVerificationData,
): readonly DataValidationIssue[] {
  const issues: DataValidationIssue[] = [];
  const report = (path: string, message: string) => issues.push({ path, message });

  const collections: ReadonlyArray<readonly [string, readonly { readonly id: string }[]]> = [
    ["repositories", data.repositories],
    ["evidence", data.evidence],
    ["clusters", data.clusters],
    ["nodes", data.nodes],
    ["edges", data.edges],
    ["stages", data.stages],
    ["development.contributors", data.development.contributors],
    ["development.references", data.development.references],
    ["development.workUnits", data.development.workUnits],
  ];

  for (const [name, values] of collections) {
    for (const id of duplicateValues(values.map((value) => value.id))) {
      report(name, `duplicate id: ${id}`);
    }
  }

  const repositories = new Set(data.repositories.map((repo) => repo.id));
  const evidence = new Map(data.evidence.map((item) => [item.id, item]));
  const clusters = new Map(data.clusters.map((cluster) => [cluster.id, cluster]));
  const nodes = new Map(data.nodes.map((node) => [node.id, node]));
  const stages = new Set(data.stages.map((stage) => stage.id));
  const contributors = new Map(
    data.development.contributors.map((contributor) => [contributor.id, contributor]),
  );
  const workReferences = new Map(
    data.development.references.map((reference) => [reference.id, reference]),
  );
  const workUnits = new Map(
    data.development.workUnits.map((workUnit) => [workUnit.id, workUnit]),
  );

  const checkRepoIds = (path: string, ids: readonly RepositoryId[]) => {
    for (const id of ids) {
      if (!repositories.has(id)) report(path, `unknown repository: ${id}`);
    }
  };
  const checkEvidenceIds = (path: string, ids: readonly string[]) => {
    for (const id of ids) {
      if (!evidence.has(id)) report(path, `unknown evidence: ${id}`);
    }
  };
  const checkStageIds = (path: string, ids: readonly string[]) => {
    for (const id of ids) {
      if (!stages.has(id)) report(path, `unknown stage: ${id}`);
    }
  };

  for (const item of data.evidence) {
    if (!repositories.has(item.repoId)) {
      report(`evidence.${item.id}.repoId`, `unknown repository: ${item.repoId}`);
    }
    if (item.publication === "public" && !item.url) {
      report(`evidence.${item.id}.url`, "public evidence must have a URL");
    }
    if (item.publication === "pending" && item.repoId !== "garden") {
      report(
        `evidence.${item.id}.publication`,
        "only the selected Garden publication target should use pending URLs",
      );
    }
    if (item.publication === "local" && item.url) {
      report(`evidence.${item.id}.url`, "local evidence must not expose a repository URL");
    }
  }

  for (const reference of data.development.references) {
    const path = `development.references.${reference.id}`;
    if (!reference.url.startsWith("https://github.com/formal-land/garden/")) {
      report(`${path}.url`, "work references must use the public formal-land/garden repository");
    }
    if (
      reference.kind === "migrated-pr" &&
      !/^https:\/\/github\.com\/formal-land\/garden\/commit\/[0-9a-f]+$/.test(
        reference.url,
      )
    ) {
      report(`${path}.url`, "migrated PRs must link to their preserved public commit");
    }
    if (reference.kind === "migrated-pr" && reference.number === undefined) {
      report(`${path}.number`, "migrated PRs require their historical number");
    }
  }

  for (const workUnit of data.development.workUnits) {
    const path = `development.workUnits.${workUnit.id}`;
    for (const contributorId of workUnit.contributorIds) {
      if (!contributors.has(contributorId)) {
        report(`${path}.contributorIds`, `unknown contributor: ${contributorId}`);
      }
    }
    for (const referenceId of workUnit.referenceIds) {
      if (!workReferences.has(referenceId)) {
        report(`${path}.referenceIds`, `unknown work reference: ${referenceId}`);
      }
    }
    if (workUnit.scope === "verification" && workUnit.status !== "completed") {
      report(`${path}.status`, "published verification work units must be completed");
    }
  }

  for (const referenceId of [
    data.development.verificationPullRequestId,
    data.development.websitePullRequestId,
  ]) {
    if (!workReferences.has(referenceId)) {
      report("development", `unknown pull-request reference: ${referenceId}`);
    }
  }

  for (const cluster of data.clusters) {
    checkRepoIds(`clusters.${cluster.id}.repoIds`, cluster.repoIds);
    for (const nodeId of cluster.nodeIds) {
      const node = nodes.get(nodeId);
      if (!node) report(`clusters.${cluster.id}.nodeIds`, `unknown node: ${nodeId}`);
      else if (node.clusterId !== cluster.id) {
        report(
          `clusters.${cluster.id}.nodeIds`,
          `node ${nodeId} points back to cluster ${node.clusterId}`,
        );
      }
    }
  }

  for (const node of data.nodes) {
    const path = `nodes.${node.id}`;
    if (!clusters.has(node.clusterId)) report(`${path}.clusterId`, `unknown cluster: ${node.clusterId}`);
    else if (!insideCluster(node, data)) report(`${path}.position`, "node position is outside its cluster bounds");
    checkRepoIds(`${path}.repoIds`, node.repoIds);
    checkEvidenceIds(`${path}.evidenceIds`, node.evidenceIds);
    checkStageIds(`${path}.stageIds`, node.stageIds);
    for (const workUnitId of node.workUnitIds) {
      const workUnit = workUnits.get(workUnitId);
      if (!workUnit) report(`${path}.workUnitIds`, `unknown work unit: ${workUnitId}`);
      else if (workUnit.scope !== "verification") {
        report(`${path}.workUnitIds`, `proof nodes cannot use publication unit: ${workUnitId}`);
      }
    }
    if (node.status !== "wip" && node.workUnitIds.length === 0) {
      report(`${path}.workUnitIds`, "non-WIP proof nodes require development provenance");
    }

    if (node.status !== "wip") {
      for (const evidenceId of node.evidenceIds) {
        if (evidence.get(evidenceId)?.status === "wip") {
          report(`${path}.evidenceIds`, `non-WIP node depends on WIP evidence: ${evidenceId}`);
        }
      }
    }
  }

  for (const edge of data.edges) {
    const path = `edges.${edge.id}`;
    const from = nodes.get(edge.from);
    const to = nodes.get(edge.to);
    if (!from) report(`${path}.from`, `unknown node: ${edge.from}`);
    if (!to) report(`${path}.to`, `unknown node: ${edge.to}`);
    checkEvidenceIds(`${path}.evidenceIds`, edge.evidenceIds);
    checkStageIds(`${path}.stageIds`, edge.stageIds);

    if (edge.family === "formal" && edge.evidenceIds.length === 0) {
      report(`${path}.evidenceIds`, "formal edges require an evidence anchor");
    }
    if (from?.status === "wip" && to?.status !== "wip" && edge.status !== "wip") {
      report(path, "WIP work cannot support an established claim");
    }
    if (edge.status !== "wip") {
      for (const evidenceId of edge.evidenceIds) {
        if (evidence.get(evidenceId)?.status === "wip") {
          report(`${path}.evidenceIds`, `established edge uses WIP evidence: ${evidenceId}`);
        }
      }
    }
  }

  const expectedOrdinals = data.stages.map((_, index) => index + 1);
  data.stages.forEach((stage, index) => {
    const path = `stages.${stage.id}`;
    if (stage.ordinal !== expectedOrdinals[index]) {
      report(`${path}.ordinal`, `expected ${expectedOrdinals[index]}, found ${stage.ordinal}`);
    }
    checkRepoIds(`${path}.repoIds`, stage.repoIds);
    checkEvidenceIds(`${path}.evidenceIds`, stage.evidenceIds);
    for (const workUnitId of stage.workUnitIds) {
      const workUnit = workUnits.get(workUnitId);
      if (!workUnit) report(`${path}.workUnitIds`, `unknown work unit: ${workUnitId}`);
      else if (workUnit.scope !== "verification") {
        report(`${path}.workUnitIds`, `journey stages cannot use publication unit: ${workUnitId}`);
      }
    }
    if (stage.workUnitIds.length === 0) {
      report(`${path}.workUnitIds`, "journey stages require development provenance");
    }
    for (const nodeId of stage.nodeIds) {
      if (!nodes.has(nodeId)) report(`${path}.nodeIds`, `unknown node: ${nodeId}`);
    }
  });

  const requiredRefs: Readonly<Record<"garden" | "halo2" | "orchard", string>> = {
    garden: "938af2a12433e420ec9da9918b0863fb99970b90",
    halo2: "cca1dd70c5ac76daa7d9773eb9a26e33ceea9a6a",
    orchard: "05d899241b7a907d9c47dc5d3d7b3aa1361d785c",
  };
  for (const [repoId, expected] of Object.entries(requiredRefs)) {
    const actual = data.snapshot.repositoryRefs[repoId as keyof typeof requiredRefs];
    if (actual !== expected) {
      report(`snapshot.repositoryRefs.${repoId}`, `expected pinned ref ${expected}, found ${actual}`);
    }
  }

  if (data.snapshot.asOf !== "2026-07-28") {
    report("snapshot.asOf", `expected 2026-07-28, found ${data.snapshot.asOf}`);
  }
  if (data.development.asOf !== "2026-07-28") {
    report("development.asOf", `expected 2026-07-28, found ${data.development.asOf}`);
  }

  const usedVerificationUnits = new Set([
    ...data.nodes.flatMap((node) => node.workUnitIds),
    ...data.stages.flatMap((stage) => stage.workUnitIds),
  ]);
  for (const workUnit of data.development.workUnits) {
    if (
      workUnit.scope === "verification" &&
      !usedVerificationUnits.has(workUnit.id)
    ) {
      report(
        `development.workUnits.${workUnit.id}`,
        "verification work unit is not mapped to the Journey or Atlas",
      );
    }
  }

  const proofStatuses = new Set<ProofStatus>(data.filters.statuses.map((item) => item.id));
  const workTracks = new Set<WorkTrack>(data.filters.tracks.map((item) => item.id));
  for (const node of data.nodes) {
    if (!proofStatuses.has(node.status)) report(`nodes.${node.id}.status`, "status has no filter option");
    if (!workTracks.has(node.track)) report(`nodes.${node.id}.track`, "track has no filter option");
  }

  return issues;
}

export function assertValidOrchardVerificationData(data: OrchardVerificationData): void {
  const issues = validateOrchardVerificationData(data);
  if (issues.length === 0) return;
  const details = issues.map((issue) => `- ${issue.path}: ${issue.message}`).join("\n");
  throw new Error(`Invalid Orchard verification data:\n${details}`);
}
