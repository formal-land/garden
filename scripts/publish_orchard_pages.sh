#!/usr/bin/env bash

set -euo pipefail

readonly PUBLISH_SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
readonly PUBLISH_REPOSITORY_ROOT="$(git -C "${PUBLISH_SCRIPT_DIR}/.." rev-parse --show-toplevel)"
readonly PUBLISH_WEB_DIRECTORY="${PUBLISH_REPOSITORY_ROOT}/web/orchard-verification"
readonly PUBLISH_DIST_DIRECTORY="${PUBLISH_WEB_DIRECTORY}/dist"
readonly PUBLISH_REMOTE="origin"
readonly PUBLISH_BRANCH="gh-pages"

cd "${PUBLISH_REPOSITORY_ROOT}"

for publish_command in git make npm npx python3; do
  if ! command -v "${publish_command}" >/dev/null 2>&1; then
    echo "Missing required command: ${publish_command}" >&2
    exit 1
  fi
done

if [[ -n "$(git status --porcelain --untracked-files=normal)" ]]; then
  echo "Refusing to publish from a worktree with uncommitted files." >&2
  echo "Commit, remove, or ignore the reported files first:" >&2
  git status --short >&2
  exit 1
fi

readonly PUBLISH_SOURCE_SHA="$(git rev-parse HEAD)"
readonly PUBLISH_SOURCE_REF="$(git symbolic-ref --quiet --short HEAD || echo "detached HEAD")"
readonly PUBLISH_REMOTE_URL="$(git remote get-url --push "${PUBLISH_REMOTE}")"

echo "Building Orchard Pages from ${PUBLISH_SOURCE_REF} (${PUBLISH_SOURCE_SHA})."

make -C Garden orchard-structure-json-from-model
npm --prefix "${PUBLISH_WEB_DIRECTORY}" ci
npm --prefix "${PUBLISH_WEB_DIRECTORY}" run build

python3 -m unittest \
  scripts.tests.test_generate_orchard_circuit_explorer \
  scripts.tests.test_generate_orchard_circuit_grid
python3 scripts/generate_orchard_circuit_explorer.py --check
python3 scripts/generate_orchard_circuit_explorer.py \
  --validate web/orchard-verification/public/data/orchard-circuit-highlevel.v1.json
python3 scripts/generate_orchard_circuit_grid.py --check

npm --prefix "${PUBLISH_WEB_DIRECTORY}" run check

readonly PUBLISH_E2E_PORT="$(
  python3 -c \
    'import socket; listener = socket.socket(); listener.bind(("127.0.0.1", 0)); print(listener.getsockname()[1]); listener.close()'
)"
(
  cd "${PUBLISH_WEB_DIRECTORY}"
  npx playwright install chromium
  ORCHARD_E2E_ORIGIN="http://127.0.0.1:${PUBLISH_E2E_PORT}" npm run test:e2e
)

git diff --exit-code

PUBLISH_DEPLOY_DIRECTORY="$(mktemp -d /tmp/garden-gh-pages.XXXXXX)"
readonly PUBLISH_DEPLOY_DIRECTORY

cleanup_publish_directory() {
  case "${PUBLISH_DEPLOY_DIRECTORY}" in
    /tmp/garden-gh-pages.*)
      rm -rf -- "${PUBLISH_DEPLOY_DIRECTORY}"
      ;;
    *)
      echo "Refusing to remove unexpected temporary path: ${PUBLISH_DEPLOY_DIRECTORY}" >&2
      ;;
  esac
}
trap cleanup_publish_directory EXIT

cp -a "${PUBLISH_DIST_DIRECTORY}/." "${PUBLISH_DEPLOY_DIRECTORY}/"
touch "${PUBLISH_DEPLOY_DIRECTORY}/.nojekyll"

for publish_output in \
  index.html \
  proof-map.html \
  circuit.html \
  circuit-grid.html \
  data/orchard-circuit-highlevel.v1.json \
  data/orchard-circuit-grid.v1.json
do
  if [[ ! -f "${PUBLISH_DEPLOY_DIRECTORY}/${publish_output}" ]]; then
    echo "Missing deployment output: ${publish_output}" >&2
    exit 1
  fi
done

PUBLISH_SYMLINK="$(
  find "${PUBLISH_DEPLOY_DIRECTORY}" -type l -print -quit
)"
readonly PUBLISH_SYMLINK
if [[ -n "${PUBLISH_SYMLINK}" ]]; then
  echo "GitHub Pages deployment must not contain symlinks: ${PUBLISH_SYMLINK}" >&2
  exit 1
fi

PUBLISH_GIT_NAME="$(git config user.name || true)"
readonly PUBLISH_GIT_NAME
PUBLISH_GIT_EMAIL="$(git config user.email || true)"
readonly PUBLISH_GIT_EMAIL
if [[ -z "${PUBLISH_GIT_NAME}" || -z "${PUBLISH_GIT_EMAIL}" ]]; then
  echo "Configure git user.name and user.email before publishing." >&2
  exit 1
fi

git -C "${PUBLISH_DEPLOY_DIRECTORY}" init --initial-branch="${PUBLISH_BRANCH}"
git -C "${PUBLISH_DEPLOY_DIRECTORY}" config user.name "${PUBLISH_GIT_NAME}"
git -C "${PUBLISH_DEPLOY_DIRECTORY}" config user.email "${PUBLISH_GIT_EMAIL}"
git -C "${PUBLISH_DEPLOY_DIRECTORY}" add --all
git -C "${PUBLISH_DEPLOY_DIRECTORY}" -c commit.gpgsign=false commit \
  --message "Deploy Garden Pages from ${PUBLISH_SOURCE_SHA}"
git -C "${PUBLISH_DEPLOY_DIRECTORY}" remote add "${PUBLISH_REMOTE}" "${PUBLISH_REMOTE_URL}"

PUBLISH_REMOTE_RECORD="$(
  git ls-remote --heads "${PUBLISH_REMOTE_URL}" "refs/heads/${PUBLISH_BRANCH}"
)"
readonly PUBLISH_REMOTE_RECORD
PUBLISH_EXPECTED_SHA="${PUBLISH_REMOTE_RECORD%%[[:space:]]*}"
readonly PUBLISH_EXPECTED_SHA

git -C "${PUBLISH_DEPLOY_DIRECTORY}" push \
  "--force-with-lease=refs/heads/${PUBLISH_BRANCH}:${PUBLISH_EXPECTED_SHA}" \
  "${PUBLISH_REMOTE}" \
  "HEAD:refs/heads/${PUBLISH_BRANCH}"

readonly PUBLISH_DEPLOY_SHA="$(
  git -C "${PUBLISH_DEPLOY_DIRECTORY}" rev-parse HEAD
)"
echo "Published ${PUBLISH_DEPLOY_SHA} to ${PUBLISH_REMOTE}/${PUBLISH_BRANCH}."
