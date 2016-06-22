// Streamlined Causal Consistency (SCC) Model
// Copyright (c) 2016, NVIDIA Corporation.  All rights reserved.
open scc

fun fence_sc[]: Event->Event { 
	(^po :> FenceSC).^po 
}
fun mp_pattern_a0[]: Event->Event { 
	( fre ).( fence_sc ).( rfe ).( fence_sc ) 
} 
pred mp_conditions {
  not acyclic[fre.^po.rfe.^po] 
  #Address = 2
  #Thread = 2
  #Read = 2
  #Write = 2
}
check mp_poscheck_a { (mp_conditions and scc) => acyclic[mp_pattern_a0] } for 6
