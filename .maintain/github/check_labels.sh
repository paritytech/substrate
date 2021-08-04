#!/usr/bin/env bash
set -e

#shellcheck source=../common/lib.sh
source "$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )/../common/lib.sh"

repo="$GITHUB_REPOSITORY"
pr="$GITHUB_PR"

ensure_labels() {
  for label in "$@"; do
    if has_label "$repo" "$pr" "$label"; then
      return 0
    fi
  done
  return 1
}

# Must have one of the following labels
releasenotes_labels=(
  'B0-silent'
  'B3-apinoteworthy'
  'B5-clientnoteworthy'
  'B7-runtimenoteworthy'
)

criticality_labels=(
  'C1-low 📌'
  'C3-medium 📣'
  'C7-high ❗️'
  'C9-critical ‼️'
)

audit_labels=(
  'D1-audited 👍'
  'D2-notlive 💤'
  'D3-trivial 🧸'
  'D5-nicetohaveaudit ⚠️'
  'D9-needsaudit 👮'
)

echo "[+] Checking release notes (B) labels"
if ensure_labels "${releasenotes_labels[@]}";  then
  echo "[+] Release notes label detected. All is well."
else
  echo "[!] Release notes label not detected. Please add one of: ${releasenotes_labels[*]}"
  exit 1
fi

echo "[+] Checking release criticality (C) labels"
if ensure_labels "${criticality_labels[@]}";  then
  echo "[+] Release criticality label detected. All is well."
else
  echo "[!] Release criticality label not detected. Please add one of: ${criticality_labels[*]}"
  exit 1
fi

if has_runtime_changes origin/master "${HEAD_SHA}"; then
  echo "[+] Runtime changes detected. Checking audit (D) labels"
  if ensure_labels "${audit_labels[@]}";  then
    echo "[+] Release audit label detected. All is well."
  else
    echo "[!] Release audit label not detected. Please add one of: ${audit_labels[*]}"
    exit 1
  fi
fi

exit 0
