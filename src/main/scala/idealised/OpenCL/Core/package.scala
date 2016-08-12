package idealised.OpenCL

package object Core {
  trait FunctionHelper {
    type T
    type R
    type F = T => R
  }

  type =:=>[TT, RR] = FunctionHelper { type T = TT; type R = RR }

  sealed trait HList {
    def length: Int
    def toList: List[Any]
  }

  case class HCons[+H, +T <: HList](head: H, tail: T) extends HList {
    def :+: [V](v: V) = HCons(v, this)

    override def length: Int = tail.length + 1
    override def toList: List[Any] = List(head) ++ tail.toList
  }

  case object HNil extends HList {
    def :+:[V](v: V) = HCons(v, this)

    override def length: Int = 0
    override def toList: List[Nothing] = List()
  }

  type :+:[H, T <: HList] = HCons[H, T]

}