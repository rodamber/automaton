package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.math._
import stainless.proof._

import set._
import SetSpecs._
import NFASpecs._

object DFA {

  def apply[State, Sym](nfa: NFA[State, Sym]): DFA[Set[State], Sym] = {

    val alphabet = nfa.alphabet
    val validStates = nfa.validStates.powerSet

    val move = {
      val pairs: Set[(Set[State], Sym)] = validStates * alphabet
      val m: Map[(Set[State], Sym), Set[State]] = Map.empty

      pairs.foldLeft(m) { (acc, sw) =>
        sw match {
          case (s, w) =>
            val s_ = nfa.epsClosure(nfa.move(s, Some(w)))
            acc + ((s, w) -> s_)
        }
      }
    }

    val initialState = nfa.epsClosure(Set(nfa.initialState))
    val isFinal = { (s: Set[State]) => s exists nfa.isFinal }

    DFA(alphabet, validStates, move, initialState, isFinal)
  }

  def lemma[State, Sym](nfa: NFA[State, Sym], states: Set[State],
                        word: List[Sym]): Boolean = {
    require(states.subsetOf(nfa.validStates) &&
            word.forall(nfa.alphabet contains _) &&
            nfa.epsClosed(states))

    nfa.run(states, word) same DFA(nfa).run(states, word)
  }.holds because {
    val dfa = DFA(nfa)

    word match {
      case Nil() => {
        (nfa.run(states, word) same dfa.run(states, word))  ==| trivial |
        (nfa.epsClosure(states) same dfa.run(states, word)) ==|
          (nfa.epsClosed(states) &&
             sameTrans(states, nfa.epsClosure(states), dfa.run(states, word))) |
        (states same dfa.run(states, word))
      }.qed

      case (w :: ws) => {
        val step = nfa.move(states, Some(w))

        assert(epsClosureIdem(nfa, step))
        assert(nfa.epsClosed(nfa.epsClosure(step)))

        (nfa.run(states, word) same dfa.run(states, word))             ==| trivial |
        (nfa.run(states, word) same dfa.run(nfa.epsClosure(step), ws)) ==|
          (lemma(nfa, nfa.epsClosure(step), ws) &&
             sameTrans(nfa.run(states, word),
                     dfa.run(nfa.epsClosure(step), ws),
                     nfa.run(nfa.epsClosure(step), ws))) |
        (nfa.run(states, word) same nfa.run(nfa.epsClosure(step), ws))
      }.qed
    }
  }

  def dfaNfaEquiv[State, Sym](nfa: NFA[State, Sym], word: List[Sym]): Boolean = {
    require(word.forall(nfa.alphabet contains _))

    val dfa = DFA(nfa)
    nfa.accepts(word) == dfa.accepts(word)
  }.holds because {
    val init = nfa.epsClosure(Set(nfa.initialState))
    val dfa = DFA(nfa)

    assert(epsClosureIdem(nfa, Set(nfa.initialState)))
    assert(powerSetSubset(nfa.validStates, init))

    lemma(nfa, init, word) &&
      sameExists(nfa.run(init, word), dfa.run(init, word), nfa.isFinal)
  }

}

case class DFA[State, Sym](
  alphabet:     Set[Sym],
  validStates:  Set[State],
  move:         Map[(State, Sym), State],
  initialState: State,
  isFinal:      State => Boolean
) {
  require { // FIXME: We could write this a little bit more nicely...
    forall { (s: State, w: Sym) =>
      (validStates.contains(s) && alphabet.contains(w)) ==>
        validStates.contains(move(s -> w))
    } &&
    validStates.contains(initialState)
  }

  def run(state: State, word: List[Sym]): State = {
    require(validStates.contains(state) && word.forall(alphabet contains _))

    word match {
      case Nil() => state
      case (w :: ws) => run(move((state, w)), ws)
    }
  }

  def accepts(word: List[Sym]): Boolean = {
    require(word.forall(alphabet contains _))
    isFinal(run(initialState, word))
  }

}

// We represent ε-moves as by passing a None() to the transition function.
// The ε character/word is never represented explicitly.

case class NFA[State, Sym](
  alphabet:     Set[Sym],
  validStates:  Set[State],
  move:         Map[(State, Option[Sym]), Set[State]],
  initialState: State,
  isFinal:      State => Boolean
) {
  require {
    forall { (s: State, w: Option[Sym]) =>
      validInput(this, s, w) ==> move((s, w)).subsetOf(validStates)
    } &&
    validStates.contains(initialState)
  }

  def move(states: Set[State], w: Option[Sym]): Set[State] = {
    require(states.subsetOf(validStates) && validSym(this, w))

    states match {
      case (x + xs) =>
        assert(validInput(this, x, w))
        move((x, w)) ++ move(xs, w)
      case _  => Set()
    }
  } // ensuring { res => res subsetOf validStates }

  def run(states: Set[State], word: List[Sym]): Set[State] = {
    require(states.subsetOf(validStates) && word.forall(alphabet contains _))

    word match {
      case Nil() => epsClosure(states)
      case (w :: ws) =>
        val newStates = move(states, Some(w))

        assert(moveValid(this, states, Some(w)))
        run(epsClosure(newStates), ws)
    }
  } ensuring { res => res subsetOf validStates }

  def epsClosure(states: Set[State]): Set[State] = {
    require(states.subsetOf(validStates) &&
              subsetIsSmallerOrEqual(states, validStates) &&
              states.size <= validStates.size)
    decreases(validStates.size - states.size + 1)

    val m = move(states, None[Sym]())
    val newStates: Set[State] = states ++ m

    assert(moveValid(this, states, None[Sym]()))
    assert(unionOfSubsetsIsSubset(states, m, validStates))

    if (states same newStates) {
      states
    } else {
      assert(subsetOfUnion(states, m))
      assert(strictSubsetIsSmaller(states, newStates))

      epsClosure(newStates)
    }
  } ensuring { _ subsetOf validStates }

  def epsClosed(states: Set[State]): Boolean = {
    require(states subsetOf validStates)
    states same epsClosure(states)
  }

  def accepts(word: List[Sym]): Boolean = {
    require(word forall(alphabet contains _))

    val start = epsClosure(Set(initialState))
    run(start, word) exists isFinal
  }

}

object NFASpecs {

  def validState[S,W](nfa: NFA[S,W], s: S): Boolean = {
    nfa.validStates.contains(s)
  }

  def validSym[S,W](nfa: NFA[S,W], w: Option[W]): Boolean = {
    w.isEmpty || nfa.alphabet.contains(w.get)
  }

  def validInput[S,W](nfa: NFA[S,W], s: S, w: Option[W]): Boolean = {
    validState(nfa, s) && validSym(nfa, w)
  }

  def moveValid[S,W](nfa: NFA[S,W], states: Set[S], w: Option[W]): Boolean = {
    require(states.subsetOf(nfa.validStates) && validSym(nfa, w))
    nfa.move(states, w) subsetOf nfa.validStates
  }.holds because {
    states match {
      case (x + xs) =>
        assert(validInput(nfa, x, w))
        assert(nfa.move((x, w)) subsetOf nfa.validStates)

        moveValid(nfa, xs, w) &&
        unionOfSubsetsIsSubset(nfa.move((x, w)),
                               nfa.move(xs, w),
                               nfa.validStates)
      case _ => trivial
    }
  }

  def lemma2[S,W](nfa: NFA[S,W], states: Set[S]): Boolean = {
    require(states subsetOf nfa.validStates)

    val closure = nfa.epsClosure(states)
    val m = nfa.move(closure, None[W]())

    closure same (closure ++ m)
  }.holds

  def epsClosureIdem[S,W](nfa: NFA[S,W], states: Set[S]): Boolean = {
    require(states subsetOf nfa.validStates)
    nfa.epsClosure(states) same nfa.epsClosure(nfa.epsClosure(states))
  }.holds because lemma2(nfa, states)

}
