package fos

import scala.collection.mutable.{Map,HashMap};



case class TypeError(msg: String) extends Exception(msg)

object Type {

  import CT._
  import Utils._

  type Class = String
  type Context = List[Pair[String, Class]]

  def typeOf(tree: Tree, ctx: Context): Class = tree match {
    case cl@ClassDef(n, s, f, c, m) =>
      try{
        cl.verifyConstructorArgs
      } catch {
        case e => throw e
      }
      val superf = c.supers
      val csuperf = c.args.filter(fd => superf.contains(Var(fd.name)) )
      val csubf = c.args.filter(fd => !superf.contains(Var(fd.name)) )
      cl.superClass match {
        case Some(scl) => scl.checkTypeArguments(csuperf map (fd => fd.tpe))
      }
      // Check this assignment integrity
      if (c.body.count(x => x.obj != "this") != 0)
        throw ClassConstructorArgsException("Constructor only allows this assignments")
      (c.body.sortBy(x => x.field) zip csubf.sortBy(x => x.name)) foreach( p => {
      if (p._1.field != p._1.rhs.name || p._1.field != p._2.name)
          throw new ClassConstructorArgsException("This assignment error")
      })
      m.foreach(md => typeOf(md, ctx:+Pair("this", cl.name)))
      cl.name
    case me@MethodDef(tp, n, a, b) =>
      val mectx = a.map(fd => Pair(fd.name, fd.tpe))
      val ctxMap = ctx.toMap
      val cl = getClassDef(ctxMap("this"))
      cl.overrideMethod(tp, n, a, b)
      val resTp = typeOf(b, mectx:::ctx)
      if (!getClassDef(resTp).isSubClassOf(tp)) throw MethodReturnException("Return type mismatch")
      tp
    case Var(n) =>
      ctx.toMap.get(n) match {
        case Some(c) => c
        case None => throw ExprException("Unbounded Variable " + Var(n) + "\n" + tree.pos.longString)
      }
    case Select(o, f) => {
      getClassDef(typeOf(o, ctx)).findField(f) match {
        case Some(x) => x.tpe
        case None => throw ExprException("No such field " + f + " exists in " + o + "\n" + tree.pos.longString)
      }
    }
    case Apply(o, m, a) =>
      getClassDef(typeOf(o, ctx)).findMethod(m) match {
        case Some(m) =>
          val args = a.map(ex => typeOf(ex, ctx))
          m.checkTypeArguments(args)
          m.tpe
        case None =>
          throw ExprException("No such method"+ m +" exists in " + o + "\n" + tree.pos.longString)
      }
    case New(c, a) =>
      getClassDef(c).checkTypeArguments(a.map(ex => typeOf(ex, ctx)))
      c
    case Cast(c, e) =>
      val etp = typeOf(e, ctx)
      if (!getClassDef(etp).isSubClassOf(c) && !getClassDef(c).isSubClassOf(etp) )
        print("Warning: " + Cast(c, e) + ", casts between two unrelated classes" + "\n" + tree.pos.longString)
      c
  }
  //   ... To complete ... 
}

case class EvaluationException(msg: String) extends Exception

object Evaluate extends (Expr => Expr) {

  import Utils._

  def apply(expr: Expr): Expr = { //if (isValue(expr)) expr else apply(eval(expr))
    if (isValue(expr)) expr
    else {
      println(expr)
      val ex = eval(expr)
      apply(ex)
    }
  }

  def eval(expr: Expr): Expr = expr match {
    case Select(o, f) =>
      if (isValue(o)) {
        val newEx = o.asInstanceOf[New]
        val cl = getClassDef(newEx.cls)
        val idx = cl.ctor.args.indexWhere(fd => fd.name == f)
        newEx.args(idx)
      }
      else Select(eval(o), f)
    case Apply(o, m, a) =>
      if (isValue(o)) {
        val newEx = o.asInstanceOf[New]
        val cl = getClassDef(newEx.cls)
        cl.findMethod(m) match {
          case Some(me) => {
            val idx = a.indexWhere(ex => !isValue(ex))
            if (idx == -1) substituteInBody(me.body, newEx, me.args zip a)
            else Apply(o, m, a.slice(0, idx):::List(eval(a(idx))):::a.slice(idx+1, a.length))
          }
          case None => throw EvaluationException("No method found")
        }
      }
      else Apply(eval(o), m, a)
    case Cast(c, e) =>
      if (isValue(e)) {
        val newEx = e.asInstanceOf[New]
        val cl = getClassDef(newEx.cls)
        if (cl.isSubClassOf(c)) newEx
        else throw EvaluationException("Cast Error")
      }
      else Cast(c, eval(e))
    case n@New(c, a) =>
      val idx = a.indexWhere(ex => !isValue(ex))
      if (idx == -1) n
      else New(c, a.slice(0, idx):::List(eval(a(idx))):::a.slice(idx+1, a.length))
    case other => other
  }

  def isValue(expr: Expr): Boolean = expr match {
    case New(c, a) => !a.exists(ex => !isValue(ex))
    case _ => false
  }

  def substituteInBody(exp: Expr, thiss: New, substs: List[(FieldDef,Expr)]): Expr = exp match {
    case Select(obj: Expr, field: String)  => Select(substituteInBody(obj, thiss, substs),field)
    case New(cls, args)                    => New(cls,args map (arg => substituteInBody(arg, thiss, substs)))
    case Cast(cls, e)                      => Cast(cls,substituteInBody(e, thiss, substs))
    case Var("this")                       => thiss
    case Var(bd) => substs find (subs => subs._1.name == bd) match {
        case None => exp
        case Some((_,sub)) => sub
      }

    case Apply(obj,method,args)            => Apply(substituteInBody(obj, thiss, substs), method, args map (arg => substituteInBody(arg, thiss, substs)))
    case _                                 => throw new EvaluationException("Apply: Forgot expression "+exp)
  }
}

object CT {

  val objectClass: String = "Object"
  private val objectClassDef = ClassDef(objectClass, null, Nil, CtrDef(objectClass, Nil, Nil, Nil) , Nil)

  var ct: Map[String, ClassDef] = new HashMap[String, ClassDef]

  add(objectClass,objectClassDef)

  def elements = ct iterator

  def lookup(classname: String): Option[ClassDef] = if(classname != null) ct get classname else None

  def add(key: String, element: ClassDef): Unit = ct += key -> element

  def delete(key: String) = ct -= key

  def clear(): Unit = {
    ct clear;
    add(objectClass,objectClassDef)
  }

}


object Utils {

  def getClassDef(className: String): ClassDef = CT lookup className match {
    case None => throw new TypeError("class "+className+" not declared")
    case Some(c: ClassDef) => c
  }
}
