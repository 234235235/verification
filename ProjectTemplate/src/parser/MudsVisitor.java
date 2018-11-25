// Generated from Muds.g4 by ANTLR 4.7.1

package parser;

import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link MudsParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface MudsVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link MudsParser#iexpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIexpr(MudsParser.IexprContext ctx);
	/**
	 * Visit a parse tree produced by {@link MudsParser#bexpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBexpr(MudsParser.BexprContext ctx);
	/**
	 * Visit a parse tree produced by {@link MudsParser#expr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExpr(MudsParser.ExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link MudsParser#vname}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVname(MudsParser.VnameContext ctx);
	/**
	 * Visit a parse tree produced by {@link MudsParser#type}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitType(MudsParser.TypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link MudsParser#act}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAct(MudsParser.ActContext ctx);
	/**
	 * Visit a parse tree produced by {@link MudsParser#prog}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProg(MudsParser.ProgContext ctx);
	/**
	 * Visit a parse tree produced by {@link MudsParser#process}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProcess(MudsParser.ProcessContext ctx);
	/**
	 * Visit a parse tree produced by {@link MudsParser#proclist}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitProclist(MudsParser.ProclistContext ctx);
	/**
	 * Visit a parse tree produced by {@link MudsParser#updatelist}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUpdatelist(MudsParser.UpdatelistContext ctx);
	/**
	 * Visit a parse tree produced by {@link MudsParser#update}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUpdate(MudsParser.UpdateContext ctx);
	/**
	 * Visit a parse tree produced by {@link MudsParser#tform}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTform(MudsParser.TformContext ctx);
}