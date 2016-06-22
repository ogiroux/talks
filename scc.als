// Streamlined Causal Consistency (SCC) Model
// Copyright (c) 2016, NVIDIA Corporation.  All rights reserved.

module scc

////////////////////////////////////////////////////////////////////////////////
// =Memory model axioms=

pred scc {
  acyclic[rf + co + fr + po_loc]     // sc per location
  acyclic[rfe + dep]                 // no thin-air values
  no fr.co & rmw                     // rmw atomicity
  irreflexive[(rf + co + fr).^cause] // causality
}

////////////////////////////////////////////////////////////////////////////////
// =Auxiliaries=

fun fence[] : MemoryEvent->MemoryEvent {
  // There is no total order among FenceAlls
  ((^po :> FenceAll).^po) - Write->Read
  +
  // There is a total order among all FenceSCs
  (^po :> FenceSC).*sc.^po
  +
  // po ending in a Release, plus C++ release sequences
  (^po :> Release).*(po_loc :> Write)
  +
  // po starting at an Acquire
  Acquire <: ^po
}
fun cause[] : MemoryEvent->MemoryEvent {
  rfe + rmw + fence
}

////////////////////////////////////////////////////////////////////////////////
// =Basic model of memory=

// Every instantiated address must be used and written to at least once
sig Address { } //{ #(address :> this) > 1 and #(Write <: address :> this) > 0 }
fact { Address = Event.address }

sig Thread { start: one Event }

// Note: po is not transitive
abstract sig Event { po: lone Event }

abstract sig MemoryEvent extends Event {
  address: one Address,
  po_loc: set MemoryEvent,
  addr: set MemoryEvent,
  data: set MemoryEvent
}
sig Read extends MemoryEvent { fr: set Write, rmw: lone Write }
sig Acquire extends Read { }
sig Write extends MemoryEvent { rf: set Read, co: lone Write }
sig Release extends Write { }

abstract sig Fence extends Event { }
sig FenceAll extends Fence { }
sig FenceSC extends FenceAll {
  sc: set FenceSC
}

////////////////////////////////////////////////////////////////////////////////
// =Constraints on basic model of memory=

// All communication is via accesses to the same address
fact { rf + co + fr in address.~address }

// Program order is sane
fact { acyclic[po] }
fact { all e: Event | one t: Thread | t->e in start.*po }
// define po_loc as a constrained basic relation rather than a function
// so that it appears in the output explicitly
fact { po_loc = ^po & address.~address }

// Dependencies go from Reads to Reads or Writes
fun dep : Read->MemoryEvent { addr + data }
fact { dep in Read <: ^po }

// co is a per-address total order
fact { all a: Address | total[co, a.~address :> Write] }

// Each read sources from at most one write
// (could be zero if sourcing from the initial condition)
fact { rf.~rf in iden }
// fr is defined in the standard way
fact { fr = (Read->Write & address.~address) - ~rf.*~co }

// RMW pairs are sane and overlap with dep
fact { rmw in po & dep & address.~address }

// sc is a total order on FenceSCs
fact { total[sc, FenceSC] }

////////////////////////////////////////////////////////////////////////////////
// =Shortcuts=

fun same_thread [rel: Event->Event] : Event->Event {
  rel & ( iden + ^po + ~^po )
}

fun com[] : MemoryEvent->MemoryEvent { rf + fr + co }
fun rfi[] : MemoryEvent->MemoryEvent { same_thread[rf] }
fun rfe[] : MemoryEvent->MemoryEvent { rf - rfi[] }
fun fri[] : MemoryEvent->MemoryEvent { same_thread[fr] }
fun fre[] : MemoryEvent->MemoryEvent { fr - fri }
fun coi[] : MemoryEvent->MemoryEvent { same_thread[co] }
fun coe[] : MemoryEvent->MemoryEvent { co - coi }

////////////////////////////////////////////////////////////////////////////////
// =Alloy helpers=

pred irreflexive[rel: Event->Event]        { no iden & rel }
pred acyclic[rel: Event->Event]            { irreflexive[^rel] }
pred total[rel: Event->Event, bag: Event] {
  all disj e, e': bag | e->e' + e'->e in ^rel + ^~rel  //rel includes everyone
  all e: bag | lone e': bag | e'->e in rel             //rel is join-free
  all e: bag | lone e': bag | e->e' in rel             //rel is fork-free
  acyclic[rel]                                         //rel has no cycles
}
