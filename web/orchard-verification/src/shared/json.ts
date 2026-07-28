export type JsonRecord = Record<string, unknown>;

export function record(value: unknown): JsonRecord {
  return value !== null && typeof value === "object" && !Array.isArray(value)
    ? value as JsonRecord
    : {};
}

export function pick(target: JsonRecord, ...keys: readonly string[]): unknown {
  for (const key of keys) {
    if (target[key] !== undefined) return target[key];
  }
  return undefined;
}

export function text(
  target: JsonRecord,
  keys: readonly string[],
  fallback = "",
): string {
  const value = pick(target, ...keys);
  return typeof value === "string" || typeof value === "number"
    ? String(value)
    : fallback;
}

export function numberValue(
  target: JsonRecord,
  keys: readonly string[],
  fallback = 0,
): number {
  const value = pick(target, ...keys);
  const parsed = typeof value === "number" ? value : Number(value);
  return Number.isFinite(parsed) ? parsed : fallback;
}

export function optionalNumber(
  target: JsonRecord,
  keys: readonly string[],
): number | undefined {
  const value = pick(target, ...keys);
  if (value === undefined || value === null || value === "") return undefined;
  const parsed = typeof value === "number" ? value : Number(value);
  return Number.isFinite(parsed) ? parsed : undefined;
}
