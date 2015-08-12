function log_stderr {
    # Prefixes lines with identifying information, to make stderr more useful
    # Use with process substitution, eg. `foo bar 2> >(log_stderr foo bar)`
    sed "s/^/[$*]: /" >&2
}

function jqLog {
    # We use jq a lot, and it has pretty cryptic error messages, so we use this
    # augmented version to make finding problems easier
    jq "$@" 2> >(log_stderr jqLog "$@")
}
