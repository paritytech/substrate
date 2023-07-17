#!/bin/bash

total_warnings=0

for d in */ ; do
    if [[ $d != "examples/" ]]; then
        cd "$d"
        # Allow all clippy linters, and then warn on specific docs related ones
        warnings=$(cargo clippy -- -A clippy::all -W clippy::missing_docs_in_private_items -W clippy::missing_errors_doc -W clippy::missing_panics_doc -W clippy::missing_safety_doc -W clippy::undocumented_unsafe_blocks -W clippy::unnecessary_safety_doc -W clippy::unnecessary_safety_comment -W clippy::allow_attributes_without_reason -W clippy::doc_link_with_quotes -W clippy::tabs_in_doc_comments -W clippy::empty_line_after_doc_comments -W clippy::suspicious_doc_comments -W clippy::doc_markdown --no-deps 2>&1 | grep "warning:" | wc -l)
        warnings=$((warnings > 0 ? warnings - 1 : 0)) # End of output also includes a line starting with 'warning:' so -1 to remove it from count
        printf "%-40s %s\n" "$d " "$warnings warnings"
        total_warnings=$((total_warnings + warnings))
        cd ..
    fi
done

printf "%-20s %s\n" "Total warnings: " "$total_warnings"