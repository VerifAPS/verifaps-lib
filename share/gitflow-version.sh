#!/bin/bash

BRANCH=$(git rev-parse --abbrev-ref HEAD)

alphaLabel="dev"
major=0
minor=0
patch=0
preReleasePrefix=
preRelease=
buildMetadata=

function parseVersion() {
    if [[ $1 =~ v?(?P<M>\d+)\.(?P<m>\d+)\.(?P<P>\d+)(-(?P<pp>.*)\.(?P<pr>\d+))?(\+(?P<b>.*))? ]]; then 
        major=${BASH_REMATCH[M]}
        minor=${BASH_REMATCH[m]}
        patch=${BASH_REMATCH[P]}
        preReleasePrefix=${BASH_REMATCH[pp]}
        preRelease=${BASH_REMATCH[pr]}
        buildMetadata=${BASH_REMATCH[b]}
    fi
}

function commitsSince() {
    git rev-list --count ${1}..HEAD
}

function describeMaster() { 
    parseVersion $(git describe)
}

function describeHotfix() {
    name=${BRANCH##hotfix/}
    commits=$(( 1 + $(commitsSince master) ))
    parseVersion "$name-rc.$commits"
}

function describeFeature() {
    describeDevelop
    preReleasePrefix="feat-${BRANCH##feature/}"        
    preRelease=$(( 1 + $(commitsSince develop) ))
}

function describeBugfix() {
    describeDevelop
    uniqueBranchId="feat-${BRANCH##bugfix/}"    
    preRelease=$(( 1 + $(commitsSince develop) ))
    preReleasePrefix="-bugfix-${uniqueBranchId}"
}

function describeDevelop() {
    gitDescribeMatchRule="*[0-9].[0-9]*.[0-9]*"
    gitOutput=$(git describe --dirty --abbrev=7 --tags --match ${gitDescribeMatchRule})
    [[ gitOutput =~ v?(?P<v>.*?)-(?P<c>[0-9]*?)-g(?P<h>[0-9a-f]+) ]]        
    parseVersion "${BASH_REMATCH[v]}-$alphaLabel.${BASH_REMATCH[c]}"
}

function describeUnknown() {
    describeDevelop
    preReleasePrefix=unknown-${BRANCH}
    preRelease=$(( 1 + $(commitsSince "develop") ))
}

case $BRANCH in 
    master)     describeMaster  ;;
    hotfix/*)   describeHotfix  ;;
    feature/*)  describeFeature ;; 
    bugfix/*)   describeBugfix  ;;     
    develop)    describeDevelop ;;    
    *)          describeUnknown ;;
esac

# Print Version:
#//[[ $1 =~ (\d+)\.(\d+)\.(\d+)(-(.*)\.(\d+))?(\+(.*))? ]]
echo -n "v$major-$minor-$patch"

[ ! -z $preReleasePrefix ] && echo -n "-$preReleasePrefix.$preRelease"
[ ! -z $buildMetadata ] && echo -n "+$buildMetadata"

echo

