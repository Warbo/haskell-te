defs: with defs;

pkg:

testMsg (isString pkg.quickBuild.time.mean.estPoint) "Quick build" &&
testMsg (isString pkg.slowBuild.time.mean.estPoint)  "Slow build"
