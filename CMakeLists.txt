# If we don't need RTTI or EH, there's no reason to export anything
# from the hello plugin.
add_llvm_loadable_module( bso_optimization
  cse.cpp
  const_prop.cpp
  licm.cpp
  ido.cpp
  alg_simplify.cpp
  livenessAnalysis.cpp
  dominanceAnalysis.cpp

  DEPENDS
  PLUGIN_TOOL
  opt
  )
