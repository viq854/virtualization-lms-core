package scala.virtualization.lms
package common

import scala.virtualization.lms.internal.{GenericFatCodegen,GenerationFailedException}
import reflect.{SourceContext, RefinedManifest}

//import test7.{ArrayLoops,ArrayLoopsExp,ArrayLoopsFatExp,ScalaGenArrayLoops,ScalaGenFatArrayLoopsFusionOpt,TransformingStuff} // TODO: eliminate deps
import util.OverloadHack
import java.io.PrintWriter

trait StructOps extends Base {

  trait Struct extends Row[Rep]

  implicit def repToStructOps(s: Rep[Struct]) = new StructOpsCls(s)
  class StructOpsCls(s: Rep[Struct]) {
    def selectDynamic[T:Manifest](index: String): Rep[T] = field(s, index)
  }

  def __new[T<:Row[Rep]:Manifest](fields: (String, Rep[T] => Rep[_])*): Rep[T] = anonStruct[T](fields)

  def anonStruct[T:Manifest](fields: Seq[(String, Rep[T] => Rep[_])]): Rep[T]

  def struct[T:Manifest](elems: (String, Rep[Any])*): Rep[T]
  def field[T:Manifest](struct: Rep[Struct], index: String): Rep[T]
}

trait StructExp extends StructOps with BaseExp with EffectExp {

  def anonStruct[T:Manifest](fields: Seq[(String, Rep[T] => Rep[_])]): Rep[T] = {
    val x = fresh[T]
    val fieldSyms = fields map { case (index, rhs) => (index, rhs(x)) }
    val fieldTypes = fieldSyms map { case (index, rhs) => (index, rhs.Type) }
    struct(fieldSyms:_*)
  }

  object Struct {
    def unapply[T](s: GenericStruct[T]): Option[(List[String], Map[String, Rep[Any]])] = Some((s.tag, s.elems))
  }

  def structName[T](m: Manifest[T]): String = m match {
    case rm: RefinedManifest[T] => "Anon_" + rm.erasure.getSimpleName + "_" + rm.fields.map(f => structName(f._2)).mkString("_")
    case _ => m.erasure.getSimpleName + m.typeArguments.map(a => structName(a)).mkString("_")
  }

  /*abstract class NewStruct[T] extends Def[T] { //base class for 'NewDSLType' nodes to allow DSL pattern-matching
    val tag: List[String]
    val elems: Map[String, Rep[Any]]
  } */ //TODO: can't bypass registerStruct

  case class GenericStruct[T](tag: List[String], elems: Map[String,Rep[Any]]) extends Def[T]
  case class Field[T:Manifest](struct: Rep[Struct], index: String) extends Def[T]

  def struct[T:Manifest](elems: (String, Rep[Any])*): Rep[T] = struct(Map(elems:_*))
  def struct[T:Manifest](elems: Map[String, Rep[Any]]): Rep[T] = struct(List(structName(manifest[T])),elems)
  def struct[T:Manifest](tag: List[String], elems: Map[String, Rep[Any]]): Rep[T] = {
    registerStruct(tag, elems)
    GenericStruct[T](tag, elems)
  }
  
  def field[T:Manifest](struct: Rep[Struct], index: String): Rep[T] = Field[T](struct, index)
  
  //FIXME: reflectMutable has to take the Def; this is overly conservative as it orders all reads (treats field read as an alloc and read)
  def mfield[T:Manifest](struct: Rep[Struct], index: String): Exp[T] = reflectMutable(Field[T](struct, index))
  def vfield[T:Manifest](struct: Rep[Struct], index: String): Variable[T] = Variable(Field[Variable[T]](struct, index))
  
  val encounteredStructs = new scala.collection.mutable.HashMap[List[String], Map[String, Manifest[Any]]]

  def registerStruct(tag: List[String], elems: Map[String, Rep[Any]]) {
    encounteredStructs(tag) = elems.map(e => (e._1,e._2.Type)) //assume tag uniquely specifies struct shape
  }

  def structType[T:Manifest] = encounteredStructs.get(List(structName(manifest[T])))

  // FIXME: need  syms override because Map is not a Product
  override def syms(x: Any): List[Sym[Any]] = x match {
    case z:Iterable[_] => z.toList.flatMap(syms)
    case _ => super.syms(x)
  }

  override def symsFreq(e: Any): List[(Sym[Any], Double)] = e match {
    case z:Iterable[_] => z.toList.flatMap(symsFreq)
    case _ => super.symsFreq(e)
  }  
  
  override def mirror[A:Manifest](e: Def[A], f: Transformer)(implicit ctx: SourceContext): Exp[A] = e match {
    case GenericStruct(tag, elems) => struct(tag, elems map { case (k,v) => (k, f(v)) })
    case _ => super.mirror(e,f)
  }
}
  
trait StructExpOpt extends StructExp {

  override def field[T:Manifest](struct: Rep[Struct], index: String): Rep[T] = struct match {
    case Def(Struct(tag, elems)) => elems(index).asInstanceOf[Rep[T]]
    case _ => super.field[T](struct, index)
  }

}

trait StructExpOptCommon extends StructExpOpt with VariablesExp with IfThenElseExp {
  
  override def var_new[T:Manifest](init: Exp[T])(implicit ctx: SourceContext): Var[T] = init match {
    case Def(Struct(tag, elems)) =>
      //val r = Variable(struct(tag, elems.mapValues(e=>var_new(e).e))) // DON'T use mapValues!! <--lazy
      Variable(struct[Variable[T]](tag, elems.map(p=>(p._1,var_new(p._2).e))))
    case _ => 
      super.var_new(init)
  }

  override def var_assign[T:Manifest](lhs: Var[T], rhs: Exp[T])(implicit ctx: SourceContext): Exp[Unit] = (lhs,rhs) match {
    case (Variable(Def(Struct(tagL,elemsL:Map[String,Exp[Variable[Any]]]))), Def(Struct(tagR, elemsR))) =>
      assert(tagL == tagR)
      assert(elemsL.keySet == elemsR.keySet)
      for (k <- elemsL.keySet)
        var_assign(Variable(elemsL(k)), elemsR(k))
      Const(())
    case _ => super.var_assign(lhs, rhs)
  }
  
  override def readVar[T:Manifest](v: Var[T])(implicit ctx: SourceContext): Exp[T] = v match {
    case Variable(Def(Struct(tag, elems: Map[String,Exp[Variable[Any]]]))) =>
      struct[T](tag, elems.map(p=>(p._1,readVar(Variable(p._2)))))
    case _ => super.readVar(v)
  }
  
  
  /*def reReify[T:Manifest](a: Rep[T]): Rep[T] = a match { // TODO: should work with loop bodies, too (Def!)
    // TODO: this seems inherently unsafe because it duplicates effects. what should we do about it?
    case Def(Reify(Def(Struct(tag,elems)),es,u)) =>
      struct[T](tag, elems.map(p=>(p._1,toAtom(Reify(p._2, es, u))))) // result is struct(reify(...))
    case _ => a
  }
  override def ifThenElse[T:Manifest](cond: Rep[Boolean], a: Rep[T], b: Rep[T]) = (reReify(a),reReify(b)) match {
    case (Def(Struct(tagA,elemsA)), Def(Struct(tagB, elemsB))) => 
      assert(tagA == tagB)
      assert(elemsA.keySet == elemsB.keySet)
      val elemsNew = for (k <- elemsA.keySet) yield (k -> ifThenElse(cond, elemsA(k), elemsB(k)))
      struct[T](tagA, elemsNew.toMap)
    case _ => super.ifThenElse(cond,a,b)
  }*/


  override def ifThenElse[T:Manifest](cond: Rep[Boolean], a: Rep[T], b: Rep[T])(implicit ctx: SourceContext) = (a,b) match {
    case (Def(Struct(tagA,elemsA)), Def(Struct(tagB, elemsB))) =>
      assert(tagA == tagB)
      assert(elemsA.keySet == elemsB.keySet)
      val elemsNew = for (k <- elemsA.keySet) yield (k -> ifThenElse(cond, elemsA(k), elemsB(k)))
      struct[T](tagA, elemsNew.toMap)
    case _ => super.ifThenElse(cond,a,b)
  }
  
}

/*

At the moment arrays still live in test case land, not in lms.common.

trait StructExpOptLoops extends StructExpOptCommon with ArrayLoopsExp {
  
  override def simpleLoop[A:Manifest](size: Exp[Int], v: Sym[Int], body: Def[A]): Exp[A] = body match {
    case ArrayElem(Def(Struct(tag, elems))) => 
      struct[A]("Array"::tag, elems.map(p=>(p._1,simpleLoop(size, v, ArrayElem(p._2)))))
    case ArrayElem(Def(ArrayIndex(b,v))) if infix_length(b) == size => b.asInstanceOf[Exp[A]] // eta-reduce! <--- should live elsewhere, not specific to struct
    case _ => super.simpleLoop(size, v, body)
  }
  
  override def infix_at[T:Manifest](a: Rep[Array[T]], i: Rep[Int]): Rep[T] = a match {
    case Def(Struct(pre::tag,elems:Map[String,Exp[Array[T]]])) =>
      assert(pre == "Array")
      struct[T](tag, elems.map(p=>(p._1,infix_at(p._2, i))))
    case _ => super.infix_at(a,i)
  }
  
  override def infix_length[T:Manifest](a: Rep[Array[T]]): Rep[Int] = a match {
    case Def(Struct(pre::tag,elems:Map[String,Exp[Array[T]]])) =>
      assert(pre == "Array")
      val ll = elems.map(p=>infix_length(p._2)) // all arrays must have same length!
      ll reduceLeft { (a1,a2) => assert(a1 == a2); a1 }
    case _ => super.infix_length(a)
  }

}
*/


// the if/phi stuff is more general than structs -- could be used for variable assignments as well

trait StructFatExp extends StructExp with BaseFatExp

trait StructFatExpOptCommon extends StructFatExp with IfThenElseFatExp { 

  case class Phi[T](cond: Exp[Boolean], a1: Exp[Unit], val thenp: Exp[T], b1: Exp[Unit], val elsep: Exp[T])(val parent: Exp[Unit]) extends AbstractIfThenElse[T] // parent points to conditional
  def phi[T:Manifest](c: Exp[Boolean], a1: Exp[Unit], a2: Exp[T], b1: Exp[Unit], b2: Exp[T])(parent: Exp[Unit]): Exp[T] = if (a2 == b2) a2 else Phi(c,a1,a2,b1,b2)(parent)

  override def syms(x: Any): List[Sym[Any]] = x match {
//    case Phi(c,a,u,b,v) => syms(List(c,a,b))
    case _ => super.syms(x)
  }

  override def symsFreq(e: Any): List[(Sym[Any], Double)] = e match {
//    case Phi(c,a,u,b,v) => freqNormal(c) ++ freqCold(a) ++ freqCold(b)
    case _ => super.symsFreq(e)
  }
  
  override def boundSyms(e: Any): List[Sym[Any]] = e match {
    case Phi(c,a,u,b,v) => effectSyms(a):::effectSyms(b)
    case _ => super.boundSyms(e)
  }

  override def mirror[A:Manifest](e: Def[A], f: Transformer)(implicit ctx: SourceContext): Exp[A] = e match {
    case p@Phi(c,a,u,b,v) => phi(f(c),f(a),f(u),f(b),f(v))(f(p.parent))
    case _ => super.mirror(e,f)
  }

  def deReify[T:Manifest](a: Rep[T]): (Rep[Unit], Rep[T]) = a match { // take Reify(stms, e) and return Reify(stms, ()), e
    case Def(Reify(x,es,u)) => (toAtom(Reify(Const(()), es, u)), x)
    case _ => (Const(()), a)
  }
  
  
  override def ifThenElse[T:Manifest](cond: Rep[Boolean], a: Rep[T], b: Rep[T])(implicit ctx: SourceContext) = (deReify(a),deReify(b)) match {
    case ((u, x@Def(Struct(tagA,elemsA))), (v, y@Def(Struct(tagB, elemsB)))) =>
      assert(tagA == tagB)
      assert(elemsA.keySet == elemsB.keySet)
      // create stm that computes all values at once
      // return struct of syms
      val combinedResult = super.ifThenElse(cond,u,v)
      
      val elemsNew = for (k <- elemsA.keySet) yield (k -> phi(cond,u,elemsA(k),v,elemsB(k))(combinedResult))
      println("----- " + combinedResult + " / " + elemsNew)
      struct[T](tagA, elemsNew.toMap)
      
    case _ => super.ifThenElse(cond,a,b)
  }



}



trait ScalaGenStruct extends ScalaGenBase {
  val IR: StructExp
  import IR._
  
  override def emitNode(sym: Sym[Any], rhs: Def[Any])(implicit stream: PrintWriter) = rhs match {
    case Struct(tag, elems) =>
      emitValDef(sym, "new " + tag.last + "(" + elems.map(e => quote(e._2)).mkString(",") + ")")
      //println("WARNING: emitting " + tag.mkString(" ") + " struct " + quote(sym))
      //emitValDef(sym, "Map(" + elems.map(e => "\"" + e._1 + "\"->" + quote(e._2)).mkString(",") + ") //" + tag.mkString(" "))
    case f@Field(struct, index) =>
      emitValDef(sym, quote(struct) + "." + index)
      //println("WARNING: emitting field access: " + quote(struct) + "." + index)
      //emitValDef(sym, quote(struct) + "(\"" + index + "\").asInstanceOf[" + remap(f.m) + "]") //FIXME: handle variable type Ref
    case _ => super.emitNode(sym, rhs)
  }

  override def remap[A](m: Manifest[A]) = m match {
    case s if s <:< manifest[Struct] => structName(m)
    case _ => super.remap(m)
  }

  override def emitDataStructures(path: String) {
    val stream = new PrintWriter(path + "Structs.scala")
    stream.println("package generated.scala")
    for ((tag, elems) <- encounteredStructs) {
      stream.println()
      stream.print("case class " + tag.mkString("") + "(")
      stream.println(elems.map(e => e._1 + ": " + remap(e._2)).mkString(", ") + ")")
    }
    stream.close()
    super.emitDataStructures(path)
  }

}

trait ScalaGenFatStruct extends ScalaGenStruct with GenericFatCodegen {
  val IR: StructFatExpOptCommon // TODO: restructure traits, maybe move this to if then else codegen?
  import IR._
  
  override def emitNode(sym: Sym[Any], rhs: Def[Any])(implicit stream: PrintWriter) = rhs match {
    case p@Phi(c,a,u,b,v) =>
      emitValDef(sym, "XXX " + rhs + " // parent " + quote(p.parent))
    case _ => super.emitNode(sym, rhs)
  }
  
  
  // TODO: implement regular fatten ?
  
  override def fattenAll(e: List[TP[Any]]): List[TTP] = {
    val m = e collect { 
      case t@TP(sym, p @ Phi(c,a,u,b,v)) => t
    } groupBy { 
      case TP(sym, p @ Phi(c,a,u,b,v)) => p.parent
    }

    //println("grouped: ")
    //println(m.mkString("\n"))

    def fatphi(s:Sym[Unit]) = {
      val phis = m(s)
      val ss = phis collect { case TP(s, _) => s }
      val us = phis collect { case TP(_, Phi(c,a,u,b,v)) => u } // assert c,a,b match
      val vs = phis collect { case TP(_, Phi(c,a,u,b,v)) => v }
      val c  = phis collect { case TP(_, Phi(c,a,u,b,v)) => c } reduceLeft { (c1,c2) => assert(c1 == c2); c1 }
      TTP(ss, SimpleFatIfThenElse(c,us,vs))
    }
    def fatif(s:Sym[Unit],c:Exp[Boolean],a:Exp[Unit],b:Exp[Unit]) = fatphi(s) match {
      case TTP(ss, SimpleFatIfThenElse(c2,us,vs)) =>
        assert(c == c2)
        TTP(s::ss, SimpleFatIfThenElse(c,a::us,b::vs))
    }

    val orphans = m.keys.toList.filterNot(k => e exists (_.sym == k)) // parent if/else might have been removed!

    val r = e.flatMap { 
      case TP(sym, p@Phi(c,a,u,b,v)) => Nil
      case TP(sym:Sym[Unit], IfThenElse(c,a:Exp[Unit],b:Exp[Unit])) => List(fatif(sym,c,a,b))
      case TP(sym:Sym[Unit], Reflect(IfThenElse(c,a:Exp[Unit],b:Exp[Unit]),_,_)) => List(fatif(sym,c,a,b))
      case t => List(fatten(t))
    } ++ orphans.map { case s: Sym[Unit] => fatphi(s) }
    
    r.foreach(println)
    r
  }
}

