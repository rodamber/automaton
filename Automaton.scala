package automaton

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang._
import stainless.math._
import stainless.proof._


object Subseq {

  def isSubseqOf[T](L: List[T], S: List[T]): Boolean = {
    (L, S) match {
      case (Nil(), _) => true
      case (_, Nil()) => false
      case (Cons(l, ls), Cons(s, ss)) => {
        if (l == s) isSubseqOf(ls, ss)
        else        isSubseqOf(L, ss)
      }
    }
  } ensuring { _ ==> (L.content subsetOf S.content) }


  @induct
  def subseqId[T](l: List[T]): Boolean = {
    isSubseqOf(l, l)
  }.holds


  def subseqProp1[T](l: List[T], x: T): Boolean = {
    isSubseqOf(l, x :: l) because {
      l match {
        case Nil()      => true
        case Cons(h, t) =>
          if (h == x) subseqProp1(t, h)
          else        subseqId(l)
      }
    }
  }.holds


  def subseqProp2[T](a: List[T], b: List[T]): Boolean = {
    require(isSubseqOf(a, b))
    a.nonEmpty ==> b.nonEmpty
  }.holds


  def subseqProp3[T](a: List[T], b: List[T]): Boolean = {
    require(a.nonEmpty)
    require(isSubseqOf(a, b))

    // FIXME:
    assert(b.nonEmpty because subseqProp2(a, b))

    (a, b) match {
      case (Cons(x, xs), Cons(y, ys)) =>
        if (x == y) isSubseqOf(xs, ys)
        else        true
    }
  }.holds


  def subseqProp4[T](a: List[T], b: List[T]): Boolean = {
    require(a.nonEmpty)
    require(isSubseqOf(a, b))

    // FIXME:
    assert(b.nonEmpty because subseqProp2(a, b))

    (a, b) match {
      case (Cons(x, _), Cons(y, ys)) =>
        if (x == y) true
        else        isSubseqOf(a, ys)
    }
  }.holds


  @induct
  def subseqTail[T](l: List[T]): Boolean = {
    l match {
      case Nil()      => true
      case Cons(h, t) => isSubseqOf(t, l) because subseqProp1(t, h)
    }
  }.holds


  // FIXME: Unverified.
  def subseqTransitive[T](a: List[T], b: List[T], c: List[T]): Boolean = {
    require(isSubseqOf(a, b))
    require(isSubseqOf(b, c))

    isSubseqOf(a, c) because {
      a match {
        case Nil()       => true
        case Cons(x, xs) =>
          assert(b.nonEmpty)

          // FIXME:
          assert(c.nonEmpty because subseqProp2(b, c))

          b match {
            case Cons(y, ys) => c match {
              case Cons(z, zs) =>
                if (x == y)
                  ((y == z) && subseqTransitive(xs, ys, zs)) || (subseqTransitive(a, b, zs))
                else subseqTransitive(a, ys, c)
            }
          }
      }
    }
  }.holds

}


import Subseq._


case class Automaton[State](
  S: List[State],                  // internal states
  M: (State, Char) => List[State], // transition function
  S0: State,                       // initial state
  F: List[State]                   // final states
) {
  // FIXME: We should probably require no repeated elements
  require(S.nonEmpty)

  require(forall((s: State, w: Char) => isSubseqOf(M(s, w), S)))

  require(isSubseqOf(List(S0), S))
  require(isSubseqOf(F, S))


  def validSet(s: List[State]): Boolean = {
    isSubseqOf(s, S)
  }


  def validSetTail(set: List[State]): Boolean = {
    require(validSet(set))

    set match {
      case Nil() => true
      case Cons(_, t) => validSet(t) because {
        subseqTail(set) && subseqTransitive(t, set, S)
      }
    }
  }.holds


  def lessThan(s: State, t: State): Boolean = {
    require(S contains s)
    require(S contains t)

    lessThanAux(s, t, S)
  }


  def lessThanAux(s: State, t: State, l: List[State]): Boolean = {
    require(l contains s)
    require(l contains t)

    l match {
      case Cons(x, xs) =>
        if      (s == x) true
        else if (t == x) false
        else             lessThanAux(s, t, xs)
    }
  }


  def move(set: List[State], w: Char): List[State] = {
    require(validSet(set))

    set match {
      case Nil()      => Nil()
      case Cons(h, t) =>
        assert(validSet(t) because validSetTail(set))
        merge(M(h, w), move(t, w))
    }
  }


  def moveSound(set: List[State], w: Char): Boolean = {
    require(validSet(set))

    validSet(move(set, w)) because {
      set match {
        case Nil()      => trivial
        case Cons(h, t) =>
          assert(validSet(t) because validSetTail(set))
          mergeSound(M(h, w), move(t, w)) && moveSound(t, w)
      }
    }
  }.holds

  // Removes repeated elements. Strictly ordered.
  def merge(a: List[State], b: List[State]): List[State] = {
    require(validSet(a))
    require(validSet(b))

    (a, b) match {
      case (_, Nil()) => a
      case (Nil(), _) => b
      case (Cons(x, xs), Cons(y, ys)) =>
        assert(validSet(xs) because validSetTail(a))

        if (x == y)              x :: merge(xs, ys)
        else if (lessThan(x, y)) x :: merge(xs, b)
        else                     y :: merge(a, ys)
    }
  }


  // FIXME: Unverified.
  def mergeSound(a: List[State], b: List[State]): Boolean = {
    require(validSet(a))
    require(validSet(b))

    validSet(merge(a, b)) because {
      (a, b) match {
        case (_, Nil()) => trivial
        case (Nil(), _) => trivial
        case (Cons(x, xs), Cons(y, ys)) =>
          assert(validSet(xs) because validSetTail(a))

          if (x == y)              mergeSound(xs, ys)
          else if (lessThan(x, y)) mergeSound(xs, b)
          else                     mergeSound(a, ys)

      }
    }
  }.holds


  // def mergeSoundLemma(x: State, xs: List[State], ys: List[State]): Boolean = {
  //   require(validSet(xs))
  //   require(validSet(x :: xs))
  //   require(validSet(ys))

  //   require(mergeSound(xs, ys))

  // }


  def isDeterministic: Boolean =
    forall { (s: State, c: Char) =>
      (S contains s) ==> (M(s, c).size <= 1)
    }


  def isAcceptingPath(states: List[State], word: List[Char]): Boolean = {
    require(states.content subsetOf S.content)

    states match {
      case Nil() => false
      case Cons(s, _) => F.contains(s) && isPath(states, word, S0)
    }
  }


  def isPath(states: List[State], word: List[Char], from: State): Boolean = {
    require(states.content subsetOf S.content)
    require(S contains from)

    (states, word) match {
      case (Cons(s, Nil()), Nil()) =>
        from == s
      case (Cons(t, ss @ Cons(s, _)), Cons(w, ws)) =>
        M(s, w).contains(t) && isPath(ss, ws, from)
      case _ =>
        false
    }
  }


  def mkPath(word: List[Char], from: State): Option[List[State]] = {
    require(S contains from)

    word match {
      case Nil()       => Some(List(from))
      case Cons(w, ws) => mkPath(ws, from) match {
        case Some(path) => path match {
          case Cons(s, _) => M(s, w) match {
            case Cons(t, _) => Some(t :: path)
            case Nil()      => None()
          }
        }
        case None() => None()
      }
    }
  }

  // Returns the set of possible states the NFA might be in after processing the
  // word.
  def runFrom(word: List[Char], from: List[State]): List[State] = {
    require(validSet(from))

    word match {
      case Nil()       => from
      case Cons(w, ws) =>
        val m = move(from, w)

        assert(validSet(m) because moveSound(from, w))
        runFrom(ws, m)
    }
  } ensuring { validSet(_) }


  // Run starting from the initial state.
  def run(word: List[Char]): List[State] = {
    runFrom(word, List(S0))
  } ensuring { validSet(_) }


  def accepts(word: List[Char]): Boolean = {
    (run(word) & F).nonEmpty
  }


  def validSubsets(set: List[State]): List[List[State]] = {
    require(validSet(set))

    set match {
      case Nil()      => List(Nil())
      case Cons(h, t) =>
        assert(validSet(t) because validSetTail(set))
        val ps = validSubsets(t)

        // FIXME: Uses map...
        ps ++ ps.map { h :: _ }
    }
  }


  // FIXME: Unverified.
  def validSubsetsSound(set: List[State]): Boolean = {
    require(validSet(set))
    validSubsets(set).forall { validSet(_) }
  }.holds


  // FIXME: adt invariant?
  def det(): Automaton[List[State]] = {
    assert(validSet(S) because subseqId(S))

    val valid   = validSubsets(S)
    val trans   = { (s: List[State], w: Char) => List(move(s, w)) }
    val initial = List(S0)
    val final_  = for (s <- valid if (s & F).nonEmpty) yield s

    Automaton(valid, trans, initial, final_)
  } ensuring { _.isDeterministic }


  // FIXME: Unverified.
  def detSound1(word: List[Char]): Boolean = {
    run(word) == det().run(word).head
  }.holds


  // FIXME: Unverified.
  def detSound2(word: List[Char]): Boolean = {
    accepts(word) == det().accepts(word)
  }.holds


}
