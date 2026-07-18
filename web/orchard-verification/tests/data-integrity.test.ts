import { existsSync, readFileSync } from "node:fs";
import { resolve } from "node:path";

import { describe, expect, it } from "vitest";

import { orchardVerificationData as data } from "../src/data/content";
import type {
  EvidenceRef,
  ProofEdge,
  ProofStatus,
  PublicationStatus,
} from "../src/data/model";

const GARDEN_ROOT = resolve(process.cwd(), "../..");

const REPOSITORY_IDS = ["garden", "halo2", "orchard", "protocol"] as const;
const PROOF_STATUSES = [
  "proved",
  "checked",
  "implemented",
  "assumption",
  "boundary",
  "wip",
] as const satisfies readonly ProofStatus[];
const PUBLICATION_STATUSES = [
  "public",
  "pending",
  "local",
] as const satisfies readonly PublicationStatus[];
const WORK_TRACKS = [
  "capture",
  "parity",
  "semantics",
  "foundations",
  "gadgets",
  "action",
  "balance",
  "engineering",
  "trust",
] as const;
const EVIDENCE_KINDS = [
  "commit",
  "source",
  "theorem",
  "documentation",
  "artifact",
  "report",
  "specification",
] as const;
const FORMAL_RELATIONS = [
  "proves",
  "entails",
  "depends-on",
  "composes",
  "limits",
] as const;
const PROVENANCE_RELATIONS = [
  "serializes",
  "matches",
  "models",
  "derives-from",
  "validates",
  "repairs",
] as const;

function expectUnique(label: string, values: readonly string[]): void {
  const duplicates = values.filter((value, index) => values.indexOf(value) !== index);
  expect(duplicates, `${label} contains duplicate IDs`).toEqual([]);
}

function expectSameMembers(
  actual: readonly string[],
  expected: readonly string[],
  label: string,
): void {
  expect([...new Set(actual)].sort(), label).toEqual([...new Set(expected)].sort());
}

function evidenceFor(ids: readonly string[]): EvidenceRef[] {
  const evidenceById = new Map(data.evidence.map((item) => [item.id, item]));
  return ids.flatMap((id) => {
    const item = evidenceById.get(id);
    return item ? [item] : [];
  });
}

describe("Orchard verification evidence model", () => {
  it("uses unique IDs in every addressable collection", () => {
    expectUnique("repositories", data.repositories.map(({ id }) => id));
    expectUnique("evidence", data.evidence.map(({ id }) => id));
    expectUnique("clusters", data.clusters.map(({ id }) => id));
    expectUnique("nodes", data.nodes.map(({ id }) => id));
    expectUnique("edges", data.edges.map(({ id }) => id));
    expectUnique("stages", data.stages.map(({ id }) => id));

    for (const repository of data.repositories) {
      expectUnique(
        `${repository.id} revisions`,
        repository.revisions.map(({ ref }) => ref),
      );
    }
    for (const group of Object.values(data.filters)) {
      expectUnique("filter options", group.map(({ id }) => id));
    }
  });

  it("only uses the declared repository, status, track, kind, and relation vocabularies", () => {
    expectSameMembers(
      data.repositories.map(({ id }) => id),
      REPOSITORY_IDS,
      "repository vocabulary",
    );

    for (const repository of data.repositories) {
      for (const revision of repository.revisions) {
        expect(PUBLICATION_STATUSES).toContain(revision.publication);
      }
    }
    for (const evidence of data.evidence) {
      expect(REPOSITORY_IDS).toContain(evidence.repoId);
      expect(PROOF_STATUSES).toContain(evidence.status);
      expect(PUBLICATION_STATUSES).toContain(evidence.publication);
      expect(EVIDENCE_KINDS).toContain(evidence.kind);
    }
    for (const item of [...data.clusters, ...data.nodes]) {
      expect(PROOF_STATUSES).toContain(item.status);
      expect(WORK_TRACKS).toContain(item.track);
      for (const repoId of item.repoIds) expect(REPOSITORY_IDS).toContain(repoId);
    }
    for (const stage of data.stages) {
      expect(PROOF_STATUSES).toContain(stage.status);
      for (const track of stage.tracks) expect(WORK_TRACKS).toContain(track);
      for (const repoId of stage.repoIds) expect(REPOSITORY_IDS).toContain(repoId);
    }
    for (const edge of data.edges) {
      expect(PROOF_STATUSES).toContain(edge.status);
      if (edge.family === "formal") expect(FORMAL_RELATIONS).toContain(edge.relation);
      else expect(PROVENANCE_RELATIONS).toContain(edge.relation);
    }

    expectSameMembers(
      data.filters.repositories.map(({ id }) => id),
      REPOSITORY_IDS,
      "repository filters",
    );
    expectSameMembers(
      data.filters.statuses.map(({ id }) => id),
      PROOF_STATUSES,
      "status filters",
    );
    expectSameMembers(
      data.filters.tracks.map(({ id }) => id),
      WORK_TRACKS,
      "track filters",
    );
  });

  it("has no dangling repository, evidence, cluster, node, edge, or stage references", () => {
    const repositoryIds = new Set(data.repositories.map(({ id }) => id));
    const evidenceIds = new Set(data.evidence.map(({ id }) => id));
    const clusterIds = new Set(data.clusters.map(({ id }) => id));
    const nodeIds = new Set(data.nodes.map(({ id }) => id));
    const stageIds = new Set(data.stages.map(({ id }) => id));

    for (const evidence of data.evidence) {
      expect(repositoryIds.has(evidence.repoId), evidence.id).toBe(true);
    }
    for (const cluster of data.clusters) {
      for (const repoId of cluster.repoIds) {
        expect(repositoryIds.has(repoId), `${cluster.id} -> repository ${repoId}`).toBe(true);
      }
      for (const nodeId of cluster.nodeIds) {
        expect(nodeIds.has(nodeId), `${cluster.id} -> node ${nodeId}`).toBe(true);
        expect(data.nodes.find(({ id }) => id === nodeId)?.clusterId).toBe(cluster.id);
      }
    }
    for (const node of data.nodes) {
      expect(clusterIds.has(node.clusterId), `${node.id} -> cluster ${node.clusterId}`).toBe(true);
      expect(data.clusters.find(({ id }) => id === node.clusterId)?.nodeIds).toContain(node.id);
      for (const repoId of node.repoIds) {
        expect(repositoryIds.has(repoId), `${node.id} -> repository ${repoId}`).toBe(true);
      }
      for (const evidenceId of node.evidenceIds) {
        expect(evidenceIds.has(evidenceId), `${node.id} -> evidence ${evidenceId}`).toBe(true);
      }
      for (const stageId of node.stageIds) {
        expect(stageIds.has(stageId), `${node.id} -> stage ${stageId}`).toBe(true);
      }
    }
    for (const edge of data.edges) {
      expect(nodeIds.has(edge.from), `${edge.id} -> from ${edge.from}`).toBe(true);
      expect(nodeIds.has(edge.to), `${edge.id} -> to ${edge.to}`).toBe(true);
      expect(edge.from, `${edge.id} must connect two different nodes`).not.toBe(edge.to);
      for (const evidenceId of edge.evidenceIds) {
        expect(evidenceIds.has(evidenceId), `${edge.id} -> evidence ${evidenceId}`).toBe(true);
      }
      for (const stageId of edge.stageIds) {
        expect(stageIds.has(stageId), `${edge.id} -> stage ${stageId}`).toBe(true);
      }
    }
    for (const stage of data.stages) {
      for (const repoId of stage.repoIds) {
        expect(repositoryIds.has(repoId), `${stage.id} -> repository ${repoId}`).toBe(true);
      }
      for (const nodeId of stage.nodeIds) {
        expect(nodeIds.has(nodeId), `${stage.id} -> node ${nodeId}`).toBe(true);
      }
      for (const evidenceId of stage.evidenceIds) {
        expect(evidenceIds.has(evidenceId), `${stage.id} -> evidence ${evidenceId}`).toBe(true);
      }
    }
  });

  it("covers the complete twelve-stage journey in order", () => {
    expect(data.stages).toHaveLength(12);
    expect(data.stages.map(({ ordinal }) => ordinal)).toEqual(
      Array.from({ length: 12 }, (_, index) => index + 1),
    );
    expect(data.stages[0].id).toBe("stage-1-groundwork");
    expect(data.stages.at(-1)?.id).toBe("stage-12-boundary");

    for (const stage of data.stages) {
      expect(stage.nodeIds.length, `${stage.id} nodes`).toBeGreaterThan(0);
      expect(stage.evidenceIds.length, `${stage.id} evidence`).toBeGreaterThan(0);
      expect(stage.established.length, `${stage.id} established facts`).toBeGreaterThan(0);
      expect(stage.carried.length, `${stage.id} carried facts`).toBeGreaterThan(0);
      expect(stage.date, `${stage.id} date`).not.toHaveLength(0);
    }

    for (const node of data.nodes) {
      expect(node.stageIds.length, `${node.id} stage coverage`).toBeGreaterThan(0);
    }
  });

  it("pins the evidence snapshot and upstream exporter revisions", () => {
    expect(data.snapshot.repositoryRefs.garden).toMatch(/^8d99eee[0-9a-f]*$/);
    expect(data.snapshot.repositoryRefs.halo2).toMatch(/^6fcb5136[0-9a-f]*$/);
    expect(data.snapshot.repositoryRefs.orchard).toMatch(/^8da8641[0-9a-f]*$/);

    const revisions = new Map(
      data.repositories.map((repository) => [
        repository.id,
        repository.revisions.map(({ ref }) => ref),
      ]),
    );
    expect(revisions.get("garden")).toContain(data.snapshot.repositoryRefs.garden);
    expect(revisions.get("halo2")).toContain(data.snapshot.repositoryRefs.halo2);
    expect(revisions.get("orchard")).toContain(data.snapshot.repositoryRefs.orchard);
    expect(revisions.get("orchard")).toContain("5b9b5c7");
  });

  it("keeps publication state explicit and local work out of established claims", () => {
    for (const evidence of data.evidence) {
      if (evidence.publication === "public") {
        expect(evidence.url, `${evidence.id} public URL`).toMatch(/^https:\/\//);
      }
      if (evidence.publication === "pending") {
        expect(evidence.repoId, `${evidence.id} pending repository`).toBe("garden");
        expect(evidence.url, `${evidence.id} future public URL`).toMatch(/^https:\/\//);
      }
      if (evidence.publication === "local") {
        expect(evidence.status, `${evidence.id} local status`).toBe("wip");
        expect(evidence.url, `${evidence.id} must not imply publication`).toBeUndefined();
      }
    }

    const consumers: Array<{ id: string; status: ProofStatus; evidenceIds: readonly string[] }> = [
      ...data.nodes,
      ...data.edges,
      ...data.stages,
    ];
    for (const consumer of consumers) {
      if (!(["proved", "checked", "implemented"] as const).includes(
        consumer.status as "proved" | "checked" | "implemented",
      )) continue;
      expect(
        evidenceFor(consumer.evidenceIds).filter(({ status }) => status === "wip"),
        `${consumer.id} must not use WIP evidence to support a non-WIP claim`,
      ).toEqual([]);
    }
  });

  it("anchors formal edges in theorem or source evidence", () => {
    const formalEdges = data.edges.filter(
      (edge): edge is Extract<ProofEdge, { family: "formal" }> => edge.family === "formal",
    );
    expect(formalEdges.length).toBeGreaterThan(0);

    for (const edge of formalEdges) {
      if (edge.relation === "limits") continue;
      const anchors = evidenceFor(edge.evidenceIds).filter(
        (item) =>
          (item.kind === "theorem" || item.kind === "source") &&
          Boolean(item.anchor?.path),
      );
      expect(anchors.length, `${edge.id} formal anchors`).toBeGreaterThan(0);
    }
  });

  it("keeps current Garden source anchors resolvable at the pinned snapshot", () => {
    const currentGardenAnchors = data.evidence.filter(
      (item) =>
        item.repoId === "garden" &&
        Boolean(item.anchor) &&
        !item.tags?.includes("side-branch") &&
        !item.tags?.includes("local-only"),
    );
    expect(currentGardenAnchors.length).toBeGreaterThan(0);

    for (const evidence of currentGardenAnchors) {
      const anchor = evidence.anchor!;
      expect(anchor.path, evidence.id).not.toMatch(/^(?:\/|\.\.\/)/);
      const sourcePath = resolve(GARDEN_ROOT, anchor.path);
      expect(existsSync(sourcePath), `${evidence.id}: ${anchor.path}`).toBe(true);
      if (anchor.symbol) {
        const source = readFileSync(sourcePath, "utf8");
        for (const symbol of anchor.symbol.split(/\s*\/\s*/)) {
          const localName = symbol.split(".").at(-1)!;
          expect(source, `${evidence.id}: symbol ${symbol}`).toContain(localName);
        }
      }
    }
  });
});
