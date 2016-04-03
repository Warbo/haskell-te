defs: with defs;

pkg:

assertMsg (isString pkg.quickBuild.time.mean.estPoint) "Quick build" &&
assertMsg (isString pkg.slowBuild.time.mean.estPoint)  "Slow build"
