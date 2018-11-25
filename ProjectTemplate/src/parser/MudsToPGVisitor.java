// Generated from Muds.g4 by ANTLR 4.7.1

package parser;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.AbstractParseTreeVisitor;
import org.antlr.v4.runtime.tree.TerminalNode;
import java.util.*;

import mudspg.*;

import parser.MudsParser.ProcessContext;
import parser.MudsParser.ProgContext;
import parser.MudsParser.TformContext;
import parser.MudsParser.TypeContext;
import parser.MudsParser.UpdateContext;

/**
 * ASTNodehis class provides an empty implementation of {@link MudsVisitor},
 * which can be extended to create a visitor which only needs to handle a subset
 * of the available methods.
 *
 * @param <ASTNode> ASTNodehe return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public class MudsToPGVisitor extends AbstractParseTreeVisitor<ASTNode> implements MudsVisitor<ASTNode> {
	
	protected ScopeMap<Variable<Integer>> ivar_scopes;
	protected ScopeMap<Variable<Boolean>> bvar_scopes;
	protected ScopeMap<Action> action_scopes;
	protected ScopeMap<TFormula> tform_scopes;

	public MudsToPGVisitor() {
		super();
		ivar_scopes = new ScopeMap<Variable<Integer>>();
		bvar_scopes = new ScopeMap<Variable<Boolean>>();
		action_scopes = new ScopeMapAction(); //Same idea, but special instance (for tau actions)
		tform_scopes = new ScopeMap<TFormula>();
	}
	
	
	/**
	 * pre-feed a set of observable variable, from current context, as if they were
	 * declared in a program p. This has to be useful when parsing a standalone
	 * temporal formula.
	 * @param ctx
	 * @param p
	 */
	public void feedObservables(ParserRuleContext ctx, Prog p) {
		for(Variable<Integer> ivar: p.ivariables) {
			ivar_scopes.extend_scope(ctx, ivar.name, ivar);
			
		}
		for(Variable<Boolean> bvar: p.bvariables) {
			bvar_scopes.extend_scope(ctx, bvar.name, bvar);
		}
	}
	
	/**
	 * {@inheritDoc}
	 *
	 * <p>ASTNodehe default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	 public Expression<Integer> visitIexpr(MudsParser.IexprContext ctx) {
		 if(ctx.vname() != null) {
			 return ivar_scopes.get_variable(ctx, ctx.vname().getText());
		 }
		 if(ctx.INT() != null) {
			 return new Constant<Integer>(Integer.parseInt(ctx.INT().getText()));
		 } else if(ctx.MULTOP() != null || ctx.ADDOP() != null) {
			 TerminalNode op = ctx.MULTOP() != null?ctx.MULTOP():ctx.ADDOP();
			 Expression<Integer> a = visitIexpr(ctx.iexpr(0));
			 Expression<Integer> b = visitIexpr(ctx.iexpr(1));
			 switch(op.getText()) {
			 case "+":
				 return new BinaryOperation.Add(a, b);
			 case "-":
				 return new BinaryOperation.Sub(a, b);
			 case "*":
				 return new BinaryOperation.Mult(a, b);
			 case "/":
				 return new BinaryOperation.Div(a, b);
			default:
				throw new ParseCancellationException("Unknown binary operation on int" + op.getText());
			 }
		 }
		 throw new ParseCancellationException("Cannot parse Iexpr:" + ctx.getText()); 
	 }
	 
	/**
	 * {@inheritDoc}
	 *
	 * <p>ASTNodehe default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	 public Expression<Boolean> visitBexpr(MudsParser.BexprContext ctx) {
		 if(ctx.vname() != null) {

			 return bvar_scopes.get_variable(ctx, ctx.vname().getText());
		 }
		 if(ctx.Btrue() != null)
		 	return Constant.true_value;
		else if(ctx.Bfalse() != null)
			return Constant.false_value;
		else if(ctx.NOT() != null)
			return new UnaryOperation.Not(visitBexpr(ctx.bexpr(0)));
		else if(ctx.children.get(0).getText().equals("("))
			return visitBexpr(ctx.bexpr(0));
		else if(ctx.CMP() != null) {
			Expression<Integer> a = visitIexpr(ctx.iexpr(0));
			Expression<Integer> b = visitIexpr(ctx.iexpr(1));
			switch(ctx.CMP().getText()) {
			case "==":
				return new BinaryOperation.Eq(a, b);
			case "<>":
			case "!=":
				return new BinaryOperation.Neq(a, b);
			case "<=":
				return new BinaryOperation.Leq(a, b);
			case "<":
				return new BinaryOperation.Lt(a, b);
			case ">":
				return new BinaryOperation.Gt(a, b);
			case ">=":
				return new BinaryOperation.Geq(a, b);
			default:
				throw new ParseCancellationException("Unknown comparison operator:" + ctx.CMP().getText());
			}
		}
		else
		{
			Expression<Boolean> a = visitBexpr(ctx.bexpr(0));
			Expression<Boolean> b = visitBexpr(ctx.bexpr(1));
			switch(ctx.getChild(1).getText()) {
			case "&":
			case "&&":
				return new BinaryOperation.And(a, b);
			case "|":
			case "||":
				return new BinaryOperation.Or(a, b);
			default:
				throw new ParseCancellationException("Unknown binary boolean operator:" + ctx.getChild(1).getText());
			}
		}
	}
	/**
	 * {@inheritDoc}
	 *
	 * <p>ASTNodehe default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	 public ASTNode visitExpr(MudsParser.ExprContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>ASTNodehe default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	 public ASTNode visitVname(MudsParser.VnameContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>ASTNodehe default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	 public ASTNode visitType(TypeContext ctx) { return visitChildren(ctx); }
	/**
	 * {@inheritDoc}
	 *
	 * <p>ASTNodehe default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	 public ASTNode visitAct(MudsParser.ActContext ctx) { return visitChildren(ctx); }
	
	/**
	 * {@inheritDoc}
	 *
	 * <p>ASTNodehe default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	 public Location visitProcess(MudsParser.ProcessContext ctx) {
		 if(ctx.act() != null) {
			 Effect eff = Effect.identity;
			 if(ctx.updatelist() != null) {
				 eff = visitUpdatelist(ctx.updatelist());
			 }
			return new FireAction(action_scopes.get_variable(ctx, ctx.act().getText()), eff);
		 }
		 if(ctx.bexpr() != null) {
			 Expression<Boolean> guard = visitBexpr(ctx.bexpr());
			 Location body = visitProcess(ctx.process(0));
			 switch(ctx.getChild(0).getText()) {
			 case "when(":
				 return new When(guard, body);
			 case "if(":
				 Location body2 = visitProcess(ctx.process(1));
				 // if(g) body else body2 --> alt{::when(g) body ::when(not(g)) body2}
				 return new Alternative(new When(guard, body), new When(new UnaryOperation.Not(guard), body2));
			 case "while(":
				 // while(g) body --> do{::when(g) body ::when(not(g) break}
				 return new Do(new Alternative(new When(guard, body), new When(new UnaryOperation.Not(guard), FireAction.breakLocation)));
			 }

		 }
		 if(ctx.process(0) != null) {
				 Location a = visitProcess(ctx.process(0));
				 if( ctx.process(1) != null ) { //It a sequential op
					 Location b = visitProcess(ctx.process(1));
					 return new Sequence(a,b);
				 } else switch(ctx.getChild(0).getText()) {
				 case "{":
					 return a;
				 case "do{":
					 return new Do(a);
				 }
		 }else if(ctx.PSTOP() != null) {
			 return FireAction.stopLocation;
		 }else if(ctx.PBREAK() != null) {
			 return FireAction.breakLocation;
		 }else if(ctx.PABORT() != null) {
			 return FireAction.abortLocation;
		 }else if(ctx.proclist() != null) {
			 Collection<Location> next = visitProclist(ctx.proclist()).actual_list;
			 switch(ctx.getChild(0).getText()) {
			 case "alt{":
				 return new Alternative(next);
			 case "par{":
				 return Par.buildPar(next);
			 case "do{":
				 return new Do(next);
			 }
		 }
		 else if(ctx.getText().equals("")) {
			 //Not really a statement, but we often put extra ; at the end of line, so don't fail about this:
			 return Location.terminated;
		 }
		 throw new ParseCancellationException("Unknown process construction:" + ctx.getText());
	 }
	 
	 private class ProcListRes extends ASTNode {
		public Collection<Location> actual_list;

		public ProcListRes(Collection<Location> actual_list) {
			super();
			this.actual_list = actual_list;
		}
	 };
	/**
	 * {@inheritDoc}
	 *
	 * <p>ASTNodehe default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	 public ProcListRes visitProclist(MudsParser.ProclistContext ctx) {
		 LinkedList<Location> res = new LinkedList<Location>();
		 for(ProcessContext childctx : ctx.process()) {
			 res.add(visitProcess(childctx));

		 }
		 return new ProcListRes(res);
	 }
	/**
	 * {@inheritDoc}
	 *
	 * <p>ASTNodehe default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	 public Effect visitUpdatelist(MudsParser.UpdatelistContext ctx) {
		 Effect res = new Effect();
		 for(UpdateContext cctx: ctx.update()){
			 String vname = cctx.vname().getText();
			 //hack: x = y may fail for boolean variables as this can be (ambigious) also
			 // parsed as an int var assigned to anothe int var
			 try {
				 Variable<Boolean> var1 = bvar_scopes.get_variable(cctx, vname);
				 Variable<Boolean> var2 = bvar_scopes.get_variable(cctx, cctx.expr().getText());
				 res.addBAss(var1, var2);
				 continue; // We're done, next assignement please
			 } catch( ParseCancellationException e) {
				 //ok, failed.
			 }
			 //hack end
			 
			 if( cctx.expr().bexpr() != null) {
				 Variable<Boolean> var = bvar_scopes.get_variable(cctx, vname);
				 res.addBAss(var, visitBexpr(cctx.expr().bexpr()));
				 continue;
			 }
			 assert(cctx.expr().iexpr() != null); //should not happen thanks to previous hack
			 Variable<Integer> var = ivar_scopes.get_variable(cctx, vname);
			 res.addIAss(var, visitIexpr(cctx.expr().iexpr()));
		 }
		 return res;
	 }
	/**
	 * {@inheritDoc}
	 *
	 * <p>ASTNodehe default implementation returns the result of calling
	 * {@link #visitChildren} on {@code ctx}.</p>
	 */
	 public ASTNode visitUpdate(MudsParser.UpdateContext ctx) { return visitChildren(ctx); }
	//
	@Override
	public Prog visitProg(ProgContext ctx) {
		if(ctx.process() != null)
			return new Prog(visitProcess(ctx.process()), action_scopes.get_all_declared(ctx), ivar_scopes.get_all_declared(ctx),
					bvar_scopes.get_all_declared(ctx), tform_scopes.get_all_declared(ctx));
		String identifier = ctx.ID().getText();
		switch(ctx.getChild(0).getText()){
		case "action":
			action_scopes.extend_scope(ctx, identifier, new Action(identifier));
			break;
		case "int":
			Variable<Integer> var;
			if( ctx.iexpr() != null)
				var = new IntVariable(identifier, visitIexpr(ctx.iexpr()));
			else
				var = new IntVariable(identifier);
			ivar_scopes.extend_scope(ctx, identifier, var);
			break;
		case "bool":
			Variable<Boolean> bvar;
			if( ctx.bexpr() != null)
				bvar = new BoolVariable(identifier, visitBexpr(ctx.bexpr()));
			else
				bvar = new BoolVariable(identifier);
			bvar_scopes.extend_scope(ctx, identifier, bvar);
			break;
		case "property":
			tform_scopes.extend_scope(ctx, identifier, visitTform(ctx.tform()));
			break;
		default:
			throw new ParseCancellationException("Unknown statement:" + ctx.getChild(0).getText());
		}
		// Do the actual recursive call to prog
		return visitProg(ctx.prog());
	}

	@Override
	public TFormula visitTform(TformContext ctx) {
		if(ctx.bexpr() != null) {
			return new TFormula.Proposition(visitBexpr(ctx.bexpr()));
		}
		TFormula suba = visitTform(ctx.tform(0));
		if(ctx.tform(1) != null) {
			TFormula subb = visitTform(ctx.tform(1));
			switch(ctx.getChild(1).getText()) {
			case "&&":
				return new TFormula.And(suba,subb);
			case "||":
				return new TFormula.Or(suba,subb);
			case "U":
				return new TFormula.Until(suba,subb);
			}
		}
		if(ctx.EPATH() != null) {
			return new TFormula.Exist(suba);
		}
		if(ctx.APATH() != null) {
			return new TFormula.All(suba);
		}
		if(ctx.NEXT() != null) {
			return new TFormula.Next(suba);
		}
		if(ctx.NEXT() != null) {
			return new TFormula.Next(suba);
		}
		if(ctx.NOT() != null) {
			return new TFormula.Not(suba);
		}
		if(ctx.EVENT() != null) {
			return new TFormula.Eventually(suba);
		}
		if(ctx.GLOB() != null) {
			return new TFormula.Globally(suba);
		}
		return suba;
	}
	 
}

/**
 * The magic to know which variable (or action ?) to pick, keep also track of all declared variables (for LTS construction)
 * @author dstan
 *
 * @param <T>
 */
class ScopeMap<T> {
	
	private Hashtable<ParserRuleContext,Scope<T>> dict;
	
	public ScopeMap(){
		dict = new Hashtable<ParserRuleContext,Scope<T>>();
	}

	private Scope<T> get_scope(ParserRuleContext ctx) {
		Scope<T> res = null;
		ParserRuleContext next = ctx;
		while(next != null) {
			res = dict.get(next);
			if(res != null)
				return res;
			ctx = next;
			next = next.getParent();
		}
		// Woops, we're at the root and found nothing ? Create it …
		res = gen_default_scope();

		dict.put(ctx, res);
		return res;
	}
	
	protected Scope<T> gen_default_scope() {
		return new Scope<T>();
	}
	
	public T get_variable(ParserRuleContext ctx, String vname) {
		return get_scope(ctx).get(vname);
	}
	
	public void extend_scope(ParserRuleContext ctx, String vname, T var) {
		Scope<T> scope = dict.get(ctx);
		if(scope == null)
			scope = get_scope(ctx);
		scope = new Scope<T>(scope, vname, var);
		dict.put(ctx, scope);
	}
	
	/**
	 * Set of all declared variables in the program
	 * @param ctx
	 * @return
	 */
	public Collection<T> get_all_declared(ParserRuleContext ctx) {
		return get_scope(ctx).all_declared;
	}
}

/**
 * Special scope map for actions, always including tau action (maybe others ?)
 * @author dstan
 *
 */
class ScopeMapAction extends ScopeMap<Action> {
	protected Scope<Action> gen_default_scope() {
		Scope<Action> res = super.gen_default_scope();
		return new Scope<Action>(res, "tau", Action.tau);
	}
}

/**
 * Scope<T> provide for a given context the declared variables of type T
 * current implementation is basically a home made linked list
 * also keep track of all declared variable with an additional collection
 * @author dstan
 *
 * @param <T>
 */
class Scope<T>{
	
	protected T some_var = null;
	protected String some_vname = null;
	protected Scope<T> parent = null;
	/**
	 * Collection of all declared elements, shared with children
	 */
	public Collection<T> all_declared = null;
	
	public Scope(Scope<T> parent, String some_vname, T some_var) {
		super();
		this.some_var = some_var;
		this.some_vname = some_vname;
		this.parent = parent;
		this.all_declared = parent.all_declared;
		all_declared.add(some_var);
	}
	
	public Scope() {
		super();
		all_declared = new LinkedList<T>();
	}

	
	public T get(String vname) {
		if(some_vname != null && vname.equals(some_vname))
			return some_var;
		if(parent!=null)
			return parent.get(vname);
		throw new ParseCancellationException("Cannot find identifier " + vname + " (wrong type or not yet defined?)");
	}
}