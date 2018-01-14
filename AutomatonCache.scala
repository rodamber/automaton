package automaton

import stainless._
import stainless.collection._
import stainless.lang._
import stainless.proof._

case class MemDFA[State, Sym](
  dfa: DFA[State, Sym],
  cache: Map[(State, Sym), State]
) {
  require {
    forall { (s: State, w: Sym) =>
      cache.isDefinedAt((s, w)) ==> (dfa.move(s, w) == cache((s, w)))
    }
  }

  def move(s: State, w: Sym): (State, MemDFA[State, Sym]) = {
    cache.get((s, w)) match {
      case Some(t) => (t, this)
      case None() =>
        val t = dfa.move(s, w)
        (t, MemDFA(dfa, cache + ((s, w) -> t)))
    }
  }

  def run(state: State, word: List[Sym]): (State, MemDFA[State, Sym]) = {
    word match {
      case Nil() => (state, this)
      case (w :: ws) =>
        val (t, mem) = move(state, w)
        mem.run(t, ws)
    }
  }

  def accepts(word: List[Sym]): (Boolean, MemDFA[State, Sym]) = {
    val (s, mem) = run(dfa.initialState, word)
    (dfa.isFinal(s), mem)
  }

}

object Specs {

  def lemma[State, Sym](dfa: DFA[State, Sym], mem: MemDFA[State, Sym],
                        s: State, word: List[Sym]): Boolean = {
    require(dfa == mem.dfa)
    dfa.run(s, word) == mem.run(s, word)._1
  }.holds because {
    word match {
      case Nil() => trivial
      case (w :: ws) =>
        val (t, newMem) = mem.move(s, w)
        lemma(dfa, newMem, dfa.move(s, w), ws)
    }
  }

  def equiv[State, Sym](dfa: DFA[State, Sym], mem: MemDFA[State, Sym],
                        word: List[Sym]): Boolean = {
    require(dfa == mem.dfa)
    dfa.accepts(word) == mem.accepts(word)._1
  }.holds because lemma(dfa, mem, dfa.initialState, word)

}
