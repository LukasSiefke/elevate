package lift.core

import lift.arithmetic.NamedVar
import lift.core.semantics._
import lift.core.types._

object traversal {
  sealed abstract class Result[+T](val value: T) {
    def map[U](f: T => U): Result[U]
    def mapVisitor(f: Visitor => Visitor): Result[T]
  }

  final case class Stop[+T](override val value: T) extends Result[T](value) {
    override def map[U](f: T => U): Result[U] = Stop(f(value))
    def mapVisitor(f: Visitor => Visitor): Result[T] = this
  }

  final case class Continue[+T](override val value: T, v: Visitor) extends Result[T](value) {
    override def map[U](f: T => U): Result[U] = Continue(f(value), v)
    def mapVisitor(f: Visitor => Visitor): Result[T] = Continue(value, f(v))
  }

  class Visitor {
    def visitExpr(e: Expr): Result[Expr] = Continue(e, this)
    def visitNat(ae: Nat): Result[Nat] = Continue(ae, this)
    def visitType[T <: Type](t: T): Result[T] = Continue(t, this)
    def visitAddressSpace(a: AddressSpace): Result[AddressSpace] = Continue(a, this)
    def visitN2N(n2n: NatToNat): Result[NatToNat] = Continue(n2n, this)
    def visitN2D(n2d: NatToData): Result[NatToData] = Continue(n2d, this)
  }

  object DepthFirstLocalResult {
    def apply(expr: Expr, v: Visitor): Expr = {
      v.visitExpr(expr) match {
        case s: Stop[Expr] => s.value
        case c: Continue[Expr] =>
          val v = c.v
          c.value match {
            case i: Identifier => i.setType(v.visitType(i.t).value)
            case Lambda(x, e) =>
              Lambda(apply(x, v).asInstanceOf[Identifier], apply(e, v))(v.visitType(expr.t).value)
            case Apply(f, e) =>
              Apply(apply(f, v), apply(e, v))(v.visitType(expr.t).value)
            case DepLambda(x, e) => x match {
              case n: NatIdentifier => DepLambda[NatKind]((v.visitNat(n).value: @unchecked) match {
                case a: NamedVar => NatIdentifier(a)
              }, apply(e, v))(v.visitType(expr.t).value)
              case dt: DataTypeIdentifier => DepLambda[DataKind](v.visitType(dt).value, apply(e, v))(v.visitType(expr.t).value)
            }
            case DepApply(f, x) => x match {
              case n: Nat           => DepApply[NatKind](apply(f, v), v.visitNat(n).value)(v.visitType(expr.t).value)
              case dt: DataType     => DepApply[DataKind](apply(f, v), v.visitType(dt).value)(v.visitType(expr.t).value)
              case a: AddressSpace  => DepApply[AddressSpaceKind](apply(f, v), v.visitAddressSpace(a).value)(v.visitType(expr.t).value)
              case n2n: NatToNat    => DepApply[NatToNatKind](apply(f, v), v.visitN2N(n2n).value)(v.visitType(expr.t).value)
              case n2d: NatToData   => DepApply[NatToDataKind](apply(f, v), v.visitN2D(n2d).value)(v.visitType(expr.t).value)
            }
            case l: Literal => l.d match {
              case NatData(n)       => Literal(NatData(v.visitNat(n).value))
              case IndexData(i, n)  => Literal(IndexData(v.visitNat(i).value, v.visitNat(n).value))
              case _ => l
            }
            // could be avoided if foreign fun could be parametric
            case ForeignFunction(decl, t) =>
              ForeignFunction(decl, v.visitType(t).value)
            case p: Primitive => p.setType(v.visitType(p.t).value)
          }
      }
    }
  }

  object DepthFirstGlobalResult {
    def chain[A, B](a: Result[A], b: B,
                    visit_b: Visitor => Result[B]): Result[(A, B)] = {
      a match {
        case Stop(as) => Stop((as, b))
        case Continue(ac, vc) => visit_b(vc).map((ac, _))
      }
    }

    def chainE[A](a: Result[A], e: Expr): Result[(A, Expr)] =
      chain(a, e, apply(e, _))

    def chainN[A](a: Result[A], n: Nat): Result[(A, Nat)] =
      chain(a, n, v => v.visitNat(n))

    def chainT[A, T <: Type](a: Result[A], t: T): Result[(A, T)] =
      chain(a, t, v => v.visitType(t))

    def chainDT[A, DT <: DataType](a: Result[A], dt: DT): Result[(A, DT)] =
      chain(a, dt, v => v.visitType(dt))

    def chainA[A](a: Result[A], addr: AddressSpace): Result[(A, AddressSpace)] =
      chain(a, addr, v => v.visitAddressSpace(addr))

    def apply(expr: Expr, visit: Visitor): Result[Expr] = {
      visit.visitExpr(expr) match {
        case Stop(r) => Stop(r)
        case Continue(c, v) => c match {
          case i: Identifier => v.visitType(i.t).map(t => i.setType(t))
          case Lambda(x, e) =>
            chainT(chainE(apply(x, v), e), expr.t)
              .map{case ((x, e), t) => Lambda(x.asInstanceOf[Identifier], e)(t)}
          case Apply(f, e) =>
            //chainT(chain(apply(f, v), e, apply(e, _)), expr.t)
            //chain(apply(f, v), (e, expr.t), v => chainT(apply(e, v), expr.t))
            //apply(f, v) ==> apply(e, v) ==> chainT
            chainT(chainE(apply(f, v), e), expr.t).map { case ((f, e), t) => Apply(f, e)(t) }
          case DepLambda(x, e) => x match {
            case n: NatIdentifier => chainT(chainE(v.visitNat(n), e), expr.t)
              .map { case ((x, e), t) =>
                DepLambda[NatKind]((x: @unchecked) match { case a: NamedVar => NatIdentifier(a) }, e)(t)
              }
            case dt: DataTypeIdentifier => chainT(chainE(v.visitType(dt), e), expr.t)
              .map { case ((x, e), t) => DepLambda[DataKind](x, e)(t) }
            case a: AddressSpace => chainT(chainE(v.visitAddressSpace(a), e), expr.t)
              .map { case ((x, e), t) => DepLambda[AddressSpaceKind](x.asInstanceOf[AddressSpaceIdentifier], e)(t) }
          }
          case DepApply(f, x) => x match {
            case n: Nat => chainT(chainN(apply(f, v), n), expr.t)
              .map { case ((f, x), t) => DepApply[NatKind](f, x)(t) }
            case dt: DataType => chainT(chainDT(apply(f, v), dt), expr.t)
              .map { case ((f, x), t) => DepApply[DataKind](f, x)(t) }
            case a: AddressSpace => chainT(chainA(apply(f, v), a), expr.t)
              .map { case ((f, x), t) => DepApply[AddressSpaceKind](f, x)(t) }
          }
          case l: Literal => l.d match {
            case NatData(n) =>
              v.visitNat(n).map(r => Literal(NatData(r)))
            case IndexData(i, n) =>
              chainN(v.visitNat(i), n).map(r => Literal(IndexData(r._1, r._2)))
            case _ => Continue(l, v)
          }
          // could be avoided if foreign fun could be parametric
          case ForeignFunction(decl, t) =>
            v.visitType(t).map(ForeignFunction(decl, _))
          case p: Primitive => v.visitType(p.t).map(t => p.setType(t))
        }
      }
    }
  }

  object types {
    object DepthFirstLocalResult {
      def apply[T <: Type](ty: T, visit: Visitor): T = {
        visit.visitType(ty) match {
          case s: Stop[T] => s.value
          case c: Continue[T] =>
            val v = c.v
            (c.value match {
              case dt: DataType => data(dt, v)
              case FunType(a, b) => FunType(apply(a, v), apply(b, v))
              case DepFunType(x, t) => x match {
                  case n: NatIdentifier =>
                    DepFunType[NatKind, Type]((v.visitNat(n).value: @unchecked) match {
                      case n: NamedVar => NatIdentifier(n.name, n.range)
                    }, apply(t, v))
                  case dt: DataTypeIdentifier =>
                    DepFunType[DataKind, Type](data(dt, v), apply(t, v))
                  case a: AddressSpaceIdentifier =>
                    DepFunType[AddressSpaceKind, Type](v.visitAddressSpace(a).value.asInstanceOf[AddressSpaceIdentifier], apply(t, v))
                  case n2n: NatToNatIdentifier =>
                    DepFunType[NatToNatKind, Type](v.visitN2N(n2n).value.asInstanceOf[NatToNatIdentifier], apply(t, v))
                  case n2d: NatToDataIdentifier =>
                    DepFunType[NatToDataKind, Type](v.visitN2D(n2d).value.asInstanceOf[NatToDataIdentifier], apply(t, v))
                }
              case i: TypeIdentifier => i
            }).asInstanceOf[T]
        }
      }

      def data[DT <: DataType](dt: DT, visit: Visitor): DT = {
        visit.visitType(dt) match {
          case s: Stop[DT] => s.value
          case c: Continue[DT] =>
            val v = c.v
            (c.value match {
              case i: DataTypeIdentifier => i
              case ArrayType(n, e) => ArrayType(v.visitNat(n).value, data(e, v))
              case DepArrayType(n, fdt) => DepArrayType(v.visitNat(n).value, v.visitN2D(fdt).value)
              case TupleType(ts@_*) => TupleType(ts.map(data(_, v)): _*)
              case s: ScalarType => s
              case IndexType(n) => IndexType(v.visitNat(n).value)
              case VectorType(n, e) => VectorType(v.visitNat(n).value, data(e, v))
              case NatToDataApply(ndtf, n) =>
                val newNDTF = ndtf match {
                  case i: NatToDataIdentifier => i
                  case NatToDataLambda(x, t) => NatToDataLambda(x, data(t, v))
                }
                NatToDataApply(newNDTF, v.visitNat(n).value)
            }).asInstanceOf[DT]
        }
      }
    }

    object DepthFirstGlobalResult {
      import traversal.DepthFirstGlobalResult.chain

      def chainT[A, T <: Type](a: Result[A], t: T):Result[(A,T)] =
        chain(a, t, apply(t, _))

      def chainDT[A, DT <: DataType](a: Result[A], dt: DT):Result[(A,DT)] =
        chain(a, dt, data(dt, _))

      def apply[T <: Type](ty: T, visit: Visitor): Result[T] = {
        visit.visitType(ty) match {
          case Stop(r) => Stop(r)
          case Continue(c, v) => (c match {
            case dt: DataType => data(dt, v)
            case FunType(a, b) =>
              chainT(apply(a, v), b).map(r => FunType(r._1, r._2))
            case DepFunType(i, t) => i match {
              case dt: DataTypeIdentifier =>
                chainT(data(dt, v), t).map(r => DepFunType[DataKind, Type](r._1, r._2))
              case n: NatIdentifier =>
                chainT(v.visitNat(n), t).map(r =>
                  DepFunType[NatKind, Type]((r._1: @unchecked) match {
                    case n: NamedVar => NatIdentifier(n.name, n.range)
                  }, r._2))
            }
            case i: TypeIdentifier => Continue(i, v)
          }).asInstanceOf[Result[T]]
        }
      }

      def data[DT <: DataType](dt: DT, visit: Visitor): Result[DT] = {
        visit.visitType(dt) match {
          case Stop(r) => Stop(r)
          case Continue(c, v) => (c match {
            case i: DataTypeIdentifier => Continue(i, v)
            case ArrayType(n, e) =>
              chainDT(v.visitNat(n), e).map(r => ArrayType(r._1, r._2))
            case DepArrayType(n, fdt) =>
              chain(v.visitNat(n), fdt, _.visitN2D(fdt)).map(r => DepArrayType(r._1, r._2))
            case TupleType(ts@_*) =>
              ts.foldLeft(Continue(Vector(), v): Result[Vector[DataType]])({ case (r, t) =>
                chainDT(r, t).map(x => x._1 :+ x._2)
              }).map(ts => TupleType(ts: _*))
            case s: ScalarType => Continue(s, v)
            case IndexType(n) => v.visitNat(n).map(IndexType)
            case VectorType(n, e) =>
              chainDT(v.visitNat(n), e).map(r => VectorType(r._1, r._2))
          }).asInstanceOf[Result[DT]]
        }
      }
    }
  }
}