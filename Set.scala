package set

import stainless._
import stainless.annotation._
import stainless.collection._
import stainless.lang.{Set => _, _}
import stainless.proof._


object Set {

  def isSet[T](l: List[T]): Boolean = {
    l match {
      case Nil()       => true
      case Cons(x, xs) => !xs.contains(x) && isSet(xs)
    }
  } ensuring { res =>
    l match {
      case Nil()     => true
      case (_ :: xs) => res ==> isSet(xs)
    }
  }

  def empty[T]: Set[T] = Set(Nil[T]())

  def singleton[T](x: T): Set[T] = Set(List(x))

}

import Set._


case class Set[T](list: List[T]) {
  require(isSet(list))

  def contains(x: T): Boolean = {
    list contains x
  }

  private def content: lang.Set[T] = {
    list content
  }

  def forall(p: T => Boolean): Boolean = {
    list forall p
  }

  def +(x: T): Set[T] = {
    require(!contains(x))
    Set(x :: list)
  }

  def ++(that: Set[T]): Set[T] = {
    require(that forall { x => !contains(x) })
    Set(this.list ++ that.list)
  }

  def subsetOf(that: Set[T]): Boolean = {
    content subsetOf that.content
  }

}

