import {
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
} from "react";
import type { JourneyStage, OrchardVerificationData } from "../data/model";
import { EvidencePanel, RepositoryBadges, StatusBadge } from "./EvidencePanel";
import { ProofMap } from "./ProofMap";

const BASE_STAGE_DURATION = 9_000;

function stageDuration(stage: JourneyStage) {
  return Math.min(
    13_000,
    BASE_STAGE_DURATION + Math.max(0, stage.nodeIds.length - 3) * 650,
  );
}

function formatTime(milliseconds: number) {
  const seconds = Math.max(0, Math.floor(milliseconds / 1_000));
  return `${Math.floor(seconds / 60)}:${String(seconds % 60).padStart(2, "0")}`;
}

function stageFromHash(stages: readonly JourneyStage[]) {
  const match = window.location.hash.match(/(?:^#|&)stage=([^&]+)/);
  if (!match) return -1;
  const requested = decodeURIComponent(match[1]);
  return stages.findIndex((stage) => stage.id === requested);
}

export function JourneyView({ data }: { data: OrchardVerificationData }) {
  const initialIndex = Math.max(0, stageFromHash(data.stages));
  const arrivedWithHash = stageFromHash(data.stages) >= 0;
  const [stageIndex, setStageIndex] = useState(initialIndex);
  const [progress, setProgress] = useState(0);
  const [playing, setPlaying] = useState(false);
  const [speed, setSpeed] = useState(1);
  const [progressive, setProgressive] = useState(false);
  const [ended, setEnded] = useState(false);
  const frameRef = useRef<number | null>(null);
  const startedAtRef = useRef(0);
  const resumeOnVisible = useRef(false);
  const currentTimelineButton = useRef<HTMLButtonElement | null>(null);
  const stage = data.stages[stageIndex];
  const duration = stageDuration(stage);
  const reducedMotion = useMemo(
    () => window.matchMedia("(prefers-reduced-motion: reduce)").matches,
    [],
  );

  const stopAnimation = useCallback(() => {
    if (frameRef.current !== null) cancelAnimationFrame(frameRef.current);
    frameRef.current = null;
  }, []);

  const pause = useCallback(() => {
    stopAnimation();
    setPlaying(false);
  }, [stopAnimation]);

  const goTo = useCallback(
    (nextIndex: number, options?: { progressive?: boolean; keepPlaying?: boolean }) => {
      const bounded = Math.max(0, Math.min(data.stages.length - 1, nextIndex));
      if (!options?.keepPlaying) pause();
      setStageIndex(bounded);
      setProgress(0);
      setProgressive(Boolean(options?.progressive));
      setEnded(false);
    },
    [data.stages.length, pause],
  );

  useEffect(() => {
    const hash = `#stage=${encodeURIComponent(stage.id)}`;
    window.history.replaceState(null, "", hash);
  }, [stage.id]);

  useEffect(() => {
    currentTimelineButton.current?.scrollIntoView({
      block: "nearest",
      inline: "center",
      behavior: reducedMotion ? "auto" : "smooth",
    });
  }, [reducedMotion, stageIndex]);

  useEffect(() => {
    if (reducedMotion || arrivedWithHash) return undefined;
    const timer = window.setTimeout(() => {
      setProgressive(true);
      setPlaying(true);
    }, 1_200);
    return () => window.clearTimeout(timer);
  }, [arrivedWithHash, reducedMotion]);

  useEffect(() => {
    if (!playing) return undefined;
    const effectiveDuration = duration / speed;
    startedAtRef.current = performance.now() - progress * effectiveDuration;

    const tick = (timestamp: number) => {
      const nextProgress = (timestamp - startedAtRef.current) / effectiveDuration;
      if (nextProgress >= 1) {
        if (stageIndex === data.stages.length - 1) {
          setProgress(1);
          setEnded(true);
          setPlaying(false);
          frameRef.current = null;
          return;
        }
        setStageIndex((current) => current + 1);
        setProgress(0);
        setProgressive(true);
        startedAtRef.current = timestamp;
      } else {
        setProgress(nextProgress);
      }
      frameRef.current = requestAnimationFrame(tick);
    };

    frameRef.current = requestAnimationFrame(tick);
    return stopAnimation;
  }, [data.stages.length, duration, playing, progress, speed, stageIndex, stopAnimation]);

  useEffect(() => {
    const onKeyDown = (event: KeyboardEvent) => {
      const target = event.target as HTMLElement;
      if (/INPUT|SELECT|TEXTAREA|BUTTON/.test(target.tagName)) return;
      if (event.key === "ArrowLeft") goTo(stageIndex - 1);
      if (event.key === "ArrowRight") goTo(stageIndex + 1);
      if (event.key === " ") {
        event.preventDefault();
        setProgressive(true);
        setPlaying((current) => !current);
      }
    };
    document.addEventListener("keydown", onKeyDown);
    return () => document.removeEventListener("keydown", onKeyDown);
  }, [goTo, stageIndex]);

  useEffect(() => {
    const onVisibilityChange = () => {
      if (document.hidden && playing) {
        resumeOnVisible.current = true;
        pause();
      } else if (!document.hidden && resumeOnVisible.current) {
        resumeOnVisible.current = false;
        setPlaying(true);
      }
    };
    document.addEventListener("visibilitychange", onVisibilityChange);
    return () => document.removeEventListener("visibilitychange", onVisibilityChange);
  }, [pause, playing]);

  const priorNodes = data.stages
    .slice(0, stageIndex)
    .flatMap((item) => item.nodeIds);
  const activeNodeIndex = Math.min(
    stage.nodeIds.length - 1,
    Math.floor(Math.min(progress, 0.999_999) * Math.max(1, stage.nodeIds.length)),
  );
  const currentReveal = progressive
    ? stage.nodeIds.slice(0, activeNodeIndex + 1)
    : stage.nodeIds;
  const focusNodes = progressive
    ? stage.nodeIds.slice(Math.max(0, activeNodeIndex - 1), activeNodeIndex + 1)
    : stage.nodeIds;
  const revealedNodes = [...new Set([...priorNodes, ...currentReveal])];

  const scrubberValue = stageIndex + progress;
  const onScrub = (value: number) => {
    pause();
    const bounded = Math.max(0, Math.min(data.stages.length, value));
    const nextStage = Math.min(data.stages.length - 1, Math.floor(bounded));
    const nextProgress = bounded === data.stages.length ? 1 : bounded - nextStage;
    setStageIndex(nextStage);
    setProgress(nextProgress);
    setProgressive(true);
    setEnded(bounded === data.stages.length);
  };

  const toggleFullscreen = async () => {
    const shell = document.querySelector<HTMLElement>(".journey-shell");
    if (!shell || !document.fullscreenEnabled) return;
    if (document.fullscreenElement) await document.exitFullscreen();
    else await shell.requestFullscreen();
  };

  return (
    <main id="main-content" className="journey-shell" tabIndex={-1}>
      <section className="journey-intro" aria-labelledby="journey-title">
        <p className="eyebrow">Garden · Rocq · Evidence snapshot {data.snapshot.asOf}</p>
        <h1 id="journey-title">Orchard Verification Journey</h1>
        <p>
          Follow how the post-NU6.2 Orchard Action implementation was captured in a checked model,
          a proof of its seven public outputs, and a transaction-level balance
          argument—without hiding what remains assumed.
        </p>
      </section>

      <section className="transport" aria-label="Journey playback">
        <div className="transport__buttons">
          <button
            className="icon-button"
            type="button"
            onClick={() => goTo(stageIndex - 1)}
            disabled={stageIndex === 0}
            aria-label="Previous stage"
            title="Previous stage"
          >
            ←
          </button>
          <button
            className="play-button"
            type="button"
            onClick={() => {
              if (ended) {
                goTo(0, { progressive: true });
                setPlaying(true);
              } else {
                setProgressive(true);
                setPlaying((current) => !current);
              }
            }}
            aria-label={ended ? "Replay journey" : playing ? "Pause journey" : "Play journey"}
          >
            <span aria-hidden="true">{ended ? "↻" : playing ? "Ⅱ" : "▶"}</span>
            {ended ? "Replay" : playing ? "Pause" : "Play"}
          </button>
          <button
            className="icon-button"
            type="button"
            onClick={() => goTo(stageIndex + 1)}
            disabled={stageIndex === data.stages.length - 1}
            aria-label="Next stage"
            title="Next stage"
          >
            →
          </button>
          <button
            className="icon-button fullscreen-button"
            type="button"
            onClick={toggleFullscreen}
            aria-label="Toggle full screen"
            title="Toggle full screen"
          >
            ⛶
          </button>
        </div>
        <div className="progress-control">
          <div className="progress-control__meta">
            <span>
              Stage {stageIndex + 1} of {data.stages.length}
            </span>
            <span>
              {formatTime(progress * duration)} / {formatTime(duration)}
            </span>
          </div>
          <input
            aria-label="Journey playhead"
            type="range"
            min={0}
            max={data.stages.length}
            step={0.001}
            value={scrubberValue}
            onChange={(event) => onScrub(Number(event.target.value))}
          />
        </div>
        <label className="speed-control">
          <span className="visually-hidden">Playback speed</span>
          <select
            value={speed}
            onChange={(event) => setSpeed(Number(event.target.value))}
            aria-label="Playback speed"
          >
            <option value={0.75}>0.75×</option>
            <option value={1}>1×</option>
            <option value={1.5}>1.5×</option>
            <option value={2}>2×</option>
          </select>
        </label>
      </section>

      <nav className="stage-timeline" aria-label="Verification journey stages">
        {data.stages.map((item, index) => (
          <button
            type="button"
            key={item.id}
            ref={index === stageIndex ? currentTimelineButton : undefined}
            className={`stage-step ${index < stageIndex ? "stage-step--past" : ""} ${
              index === stageIndex ? "stage-step--current" : ""
            }`}
            onClick={() => goTo(index)}
            aria-current={index === stageIndex ? "step" : undefined}
            title={item.title}
          >
            <span className="stage-step__date">{item.date}</span>
            <span className="stage-step__label">{item.eyebrow}</span>
          </button>
        ))}
      </nav>

      <section className="journey-map" aria-label="Progressive verification atlas">
        <ProofMap
          data={data}
          compact
          focusNodeIds={focusNodes}
          revealedNodeIds={revealedNodes}
        />
      </section>

      <article className="stage-story" aria-live="polite" key={stage.id}>
        <div className="stage-story__copy">
          <div className="stage-story__meta">
            <StatusBadge status={stage.status} />
            <RepositoryBadges data={data} repoIds={stage.repoIds} />
          </div>
          <p className="chapter-label">{stage.eyebrow} · {stage.date}</p>
          <h2>{stage.title}</h2>
          <p className="stage-purpose">{stage.purpose}</p>
          <blockquote>{stage.claim}</blockquote>
          <p>{stage.narrative}</p>
        </div>
        <EvidencePanel data={data} evidenceIds={stage.evidenceIds} />
        <div className="stage-story__outcomes">
          <section>
            <h3>Established here</h3>
            <ul className="fact-list fact-list--established">
              {stage.established.map((fact) => (
                <li key={fact}>{fact}</li>
              ))}
            </ul>
          </section>
          <section>
            <h3>Still carried</h3>
            <ul className="fact-list fact-list--carried">
              {stage.carried.map((fact) => (
                <li key={fact}>{fact}</li>
              ))}
            </ul>
          </section>
        </div>
      </article>
    </main>
  );
}
