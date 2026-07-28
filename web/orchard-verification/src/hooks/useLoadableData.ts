import { useCallback, useEffect, useState } from "react";

export type DataLoader<T> = () => Promise<T>;

export function useLoadableData<T>(loader: DataLoader<T>, fallbackError: string) {
  const [data, setData] = useState<T | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [attempt, setAttempt] = useState(0);

  useEffect(() => {
    let active = true;
    setError(null);
    loader().then(
      (loaded) => {
        if (active) setData(loaded);
      },
      (reason: unknown) => {
        if (active) setError(reason instanceof Error ? reason.message : fallbackError);
      },
    );
    return () => { active = false; };
  }, [attempt, fallbackError, loader]);

  const retry = useCallback(() => {
    setData(null);
    setAttempt((current) => current + 1);
  }, []);

  return { data, error, retry };
}
