package lift.core

import lift.arithmetic.NamedVar
import lift.core.types._

object IsClosedForm {
  def apply(expr: Expr): Boolean = {
    import traversal.{Result, Continue, Stop}

    case class Visitor(boundV: Set[Identifier],
                       boundT: Set[DataTypeIdentifier],
                       boundN: Set[NamedVar],
                       boundNatDataTypeFun:Set[NatToDataIdentifier]) extends traversal.Visitor {
      override def apply(e: Expr): Result[Expr] = {
        e match {
          case i: Identifier if !boundV(i) => Stop(i)
          case Lambda(x, _) => Continue(e, this.copy(boundV = boundV + x))
          case DepLambda(x: NatIdentifier, _)       => Continue(e, this.copy(boundN = boundN + x))
          case DepLambda(x: DataTypeIdentifier, _)  => Continue(e, this.copy(boundT = boundT + x))
          case _ => Continue(e, this)
        }
      }

      override def apply(ae: Nat): Result[Nat] = visitNat(ae, boundN, this)

      override def apply[T <: Type](t: T): Result[T] = {
        case class TypeVisitor(boundT: Set[DataTypeIdentifier],
                               boundN: Set[NamedVar],
                               boundNatDataTypeFun:Set[NatToDataIdentifier]) extends traversal.Visitor {
          override def apply[U <: Type](t: U): Result[U] = {
            t match {
              case i: DataTypeIdentifier if !boundT(i) => Stop(t)
              case DepArrayType(_, elementTypeFun) => elementTypeFun match {
                case i: NatToDataIdentifier => if(boundNatDataTypeFun(i)) Stop(t) else Continue(t, this)
                case NatToDataLambda(x, _) =>  Continue(t, this.copy(boundN = boundN + x))
              }
              case DepFunType(x: NatIdentifier, _) => Continue(t, this.copy(boundN = boundN + x))
              case DepFunType(x: DataTypeIdentifier, _) => Continue(t, this.copy(boundT = boundT + x))
              case _ => Continue(t, this)
            }
          }

          override def apply(ae: Nat): Result[Nat] = visitNat(ae, boundN, this)
        }

        traversal.types.DepthFirstGlobalResult(t, TypeVisitor(boundT, boundN, boundNatDataTypeFun))
          .mapVisitor(_ => this)
      }
    }

    def visitNat(ae: Nat, bound: Set[NamedVar], v: traversal.Visitor): Result[Nat] = {
      val closed = ae.varList.foldLeft(true)({
        case (c, v: NamedVar) => c && bound(v)
        case (c, _) => c
      })
      if (closed) { Continue(ae, v) } else { Stop(ae) }
    }

    traversal.DepthFirstGlobalResult(expr, Visitor(Set(), Set(), Set(), Set())) match {
      case Stop(_) => false
      case Continue(_, _) => true
    }
  }
}
