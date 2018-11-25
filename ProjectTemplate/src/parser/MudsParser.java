// Generated from Muds.g4 by ANTLR 4.7.1

package parser;

import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class MudsParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.7.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		T__17=18, T__18=19, T__19=20, T__20=21, T__21=22, T__22=23, T__23=24, 
		T__24=25, T__25=26, PBREAK=27, PABORT=28, PSTOP=29, Btrue=30, Bfalse=31, 
		CMP=32, ADDOP=33, MULTOP=34, EPATH=35, APATH=36, NOT=37, GLOB=38, EVENT=39, 
		UNTIL=40, NEXT=41, ID=42, INT=43, WS=44, BlockComment=45, LineComment=46;
	public static final int
		RULE_iexpr = 0, RULE_bexpr = 1, RULE_expr = 2, RULE_vname = 3, RULE_type = 4, 
		RULE_act = 5, RULE_prog = 6, RULE_process = 7, RULE_proclist = 8, RULE_updatelist = 9, 
		RULE_update = 10, RULE_tform = 11;
	public static final String[] ruleNames = {
		"iexpr", "bexpr", "expr", "vname", "type", "act", "prog", "process", "proclist", 
		"updatelist", "update", "tform"
	};

	private static final String[] _LITERAL_NAMES = {
		null, "'('", "')'", "'&'", "'|'", "'int'", "'bool'", "'tau'", "'action'", 
		"';'", "'='", "'property'", "'{='", "'=}'", "'{'", "'}'", "'alt{'", "'do{'", 
		"'par{'", "'when('", "'if('", "'else'", "'while('", "'::'", "','", "'&&'", 
		"'||'", "'break'", "'abort'", "'stop'", "'true'", "'false'", null, null, 
		null, "'E'", "'A'", "'!'", "'G'", "'F'", "'U'", "'X'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, null, null, null, null, null, null, null, null, null, 
		null, null, null, "PBREAK", "PABORT", "PSTOP", "Btrue", "Bfalse", "CMP", 
		"ADDOP", "MULTOP", "EPATH", "APATH", "NOT", "GLOB", "EVENT", "UNTIL", 
		"NEXT", "ID", "INT", "WS", "BlockComment", "LineComment"
	};
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "Muds.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public MudsParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}
	public static class IexprContext extends ParserRuleContext {
		public TerminalNode INT() { return getToken(MudsParser.INT, 0); }
		public VnameContext vname() {
			return getRuleContext(VnameContext.class,0);
		}
		public List<IexprContext> iexpr() {
			return getRuleContexts(IexprContext.class);
		}
		public IexprContext iexpr(int i) {
			return getRuleContext(IexprContext.class,i);
		}
		public TerminalNode MULTOP() { return getToken(MudsParser.MULTOP, 0); }
		public TerminalNode ADDOP() { return getToken(MudsParser.ADDOP, 0); }
		public IexprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_iexpr; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitIexpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final IexprContext iexpr() throws RecognitionException {
		return iexpr(0);
	}

	private IexprContext iexpr(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		IexprContext _localctx = new IexprContext(_ctx, _parentState);
		IexprContext _prevctx = _localctx;
		int _startState = 0;
		enterRecursionRule(_localctx, 0, RULE_iexpr, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(31);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case INT:
				{
				setState(25);
				match(INT);
				}
				break;
			case ID:
				{
				setState(26);
				vname();
				}
				break;
			case T__0:
				{
				setState(27);
				match(T__0);
				setState(28);
				iexpr(0);
				setState(29);
				match(T__1);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			_ctx.stop = _input.LT(-1);
			setState(41);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,2,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(39);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,1,_ctx) ) {
					case 1:
						{
						_localctx = new IexprContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_iexpr);
						setState(33);
						if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
						setState(34);
						match(MULTOP);
						setState(35);
						iexpr(4);
						}
						break;
					case 2:
						{
						_localctx = new IexprContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_iexpr);
						setState(36);
						if (!(precpred(_ctx, 2))) throw new FailedPredicateException(this, "precpred(_ctx, 2)");
						setState(37);
						match(ADDOP);
						setState(38);
						iexpr(3);
						}
						break;
					}
					} 
				}
				setState(43);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,2,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class BexprContext extends ParserRuleContext {
		public TerminalNode Btrue() { return getToken(MudsParser.Btrue, 0); }
		public TerminalNode Bfalse() { return getToken(MudsParser.Bfalse, 0); }
		public VnameContext vname() {
			return getRuleContext(VnameContext.class,0);
		}
		public TerminalNode NOT() { return getToken(MudsParser.NOT, 0); }
		public List<BexprContext> bexpr() {
			return getRuleContexts(BexprContext.class);
		}
		public BexprContext bexpr(int i) {
			return getRuleContext(BexprContext.class,i);
		}
		public List<IexprContext> iexpr() {
			return getRuleContexts(IexprContext.class);
		}
		public IexprContext iexpr(int i) {
			return getRuleContext(IexprContext.class,i);
		}
		public TerminalNode CMP() { return getToken(MudsParser.CMP, 0); }
		public BexprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_bexpr; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitBexpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BexprContext bexpr() throws RecognitionException {
		return bexpr(0);
	}

	private BexprContext bexpr(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		BexprContext _localctx = new BexprContext(_ctx, _parentState);
		BexprContext _prevctx = _localctx;
		int _startState = 2;
		enterRecursionRule(_localctx, 2, RULE_bexpr, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(58);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,3,_ctx) ) {
			case 1:
				{
				setState(45);
				match(Btrue);
				}
				break;
			case 2:
				{
				setState(46);
				match(Bfalse);
				}
				break;
			case 3:
				{
				setState(47);
				vname();
				}
				break;
			case 4:
				{
				setState(48);
				match(NOT);
				setState(49);
				bexpr(5);
				}
				break;
			case 5:
				{
				setState(50);
				match(T__0);
				setState(51);
				bexpr(0);
				setState(52);
				match(T__1);
				}
				break;
			case 6:
				{
				setState(54);
				iexpr(0);
				setState(55);
				match(CMP);
				setState(56);
				iexpr(0);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(68);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(66);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,4,_ctx) ) {
					case 1:
						{
						_localctx = new BexprContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_bexpr);
						setState(60);
						if (!(precpred(_ctx, 4))) throw new FailedPredicateException(this, "precpred(_ctx, 4)");
						setState(61);
						match(T__2);
						setState(62);
						bexpr(5);
						}
						break;
					case 2:
						{
						_localctx = new BexprContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_bexpr);
						setState(63);
						if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
						setState(64);
						match(T__3);
						setState(65);
						bexpr(4);
						}
						break;
					}
					} 
				}
				setState(70);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class ExprContext extends ParserRuleContext {
		public IexprContext iexpr() {
			return getRuleContext(IexprContext.class,0);
		}
		public BexprContext bexpr() {
			return getRuleContext(BexprContext.class,0);
		}
		public ExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_expr; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ExprContext expr() throws RecognitionException {
		ExprContext _localctx = new ExprContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_expr);
		try {
			setState(73);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,6,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(71);
				iexpr(0);
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(72);
				bexpr(0);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class VnameContext extends ParserRuleContext {
		public TerminalNode ID() { return getToken(MudsParser.ID, 0); }
		public VnameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_vname; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitVname(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VnameContext vname() throws RecognitionException {
		VnameContext _localctx = new VnameContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_vname);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(75);
			match(ID);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TypeContext extends ParserRuleContext {
		public TypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_type; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitType(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TypeContext type() throws RecognitionException {
		TypeContext _localctx = new TypeContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_type);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(77);
			_la = _input.LA(1);
			if ( !(_la==T__4 || _la==T__5) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ActContext extends ParserRuleContext {
		public TerminalNode ID() { return getToken(MudsParser.ID, 0); }
		public ActContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_act; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitAct(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ActContext act() throws RecognitionException {
		ActContext _localctx = new ActContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_act);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(79);
			_la = _input.LA(1);
			if ( !(_la==T__6 || _la==ID) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ProgContext extends ParserRuleContext {
		public TerminalNode ID() { return getToken(MudsParser.ID, 0); }
		public ProgContext prog() {
			return getRuleContext(ProgContext.class,0);
		}
		public IexprContext iexpr() {
			return getRuleContext(IexprContext.class,0);
		}
		public BexprContext bexpr() {
			return getRuleContext(BexprContext.class,0);
		}
		public TformContext tform() {
			return getRuleContext(TformContext.class,0);
		}
		public ProcessContext process() {
			return getRuleContext(ProcessContext.class,0);
		}
		public ProgContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_prog; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitProg(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ProgContext prog() throws RecognitionException {
		ProgContext _localctx = new ProgContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_prog);
		int _la;
		try {
			setState(109);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,9,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(81);
				match(T__7);
				setState(82);
				match(ID);
				setState(83);
				match(T__8);
				setState(84);
				prog();
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(85);
				match(T__4);
				setState(86);
				match(ID);
				setState(89);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__9) {
					{
					setState(87);
					match(T__9);
					setState(88);
					iexpr(0);
					}
				}

				setState(91);
				match(T__8);
				setState(92);
				prog();
				}
				break;
			case 3:
				enterOuterAlt(_localctx, 3);
				{
				setState(93);
				match(T__5);
				setState(94);
				match(ID);
				setState(97);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__9) {
					{
					setState(95);
					match(T__9);
					setState(96);
					bexpr(0);
					}
				}

				setState(99);
				match(T__8);
				setState(100);
				prog();
				}
				break;
			case 4:
				enterOuterAlt(_localctx, 4);
				{
				setState(101);
				match(T__10);
				setState(102);
				match(ID);
				setState(103);
				match(T__9);
				setState(104);
				tform(0);
				setState(105);
				match(T__8);
				setState(106);
				prog();
				}
				break;
			case 5:
				enterOuterAlt(_localctx, 5);
				{
				setState(108);
				process(0);
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class ProcessContext extends ParserRuleContext {
		public TerminalNode PSTOP() { return getToken(MudsParser.PSTOP, 0); }
		public TerminalNode PABORT() { return getToken(MudsParser.PABORT, 0); }
		public TerminalNode PBREAK() { return getToken(MudsParser.PBREAK, 0); }
		public ActContext act() {
			return getRuleContext(ActContext.class,0);
		}
		public UpdatelistContext updatelist() {
			return getRuleContext(UpdatelistContext.class,0);
		}
		public List<ProcessContext> process() {
			return getRuleContexts(ProcessContext.class);
		}
		public ProcessContext process(int i) {
			return getRuleContext(ProcessContext.class,i);
		}
		public ProclistContext proclist() {
			return getRuleContext(ProclistContext.class,0);
		}
		public BexprContext bexpr() {
			return getRuleContext(BexprContext.class,0);
		}
		public ProcessContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_process; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitProcess(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ProcessContext process() throws RecognitionException {
		return process(0);
	}

	private ProcessContext process(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		ProcessContext _localctx = new ProcessContext(_ctx, _parentState);
		ProcessContext _prevctx = _localctx;
		int _startState = 14;
		enterRecursionRule(_localctx, 14, RULE_process, _p);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(160);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,11,_ctx) ) {
			case 1:
				{
				}
				break;
			case 2:
				{
				setState(112);
				match(PSTOP);
				}
				break;
			case 3:
				{
				setState(113);
				match(PABORT);
				}
				break;
			case 4:
				{
				setState(114);
				match(PBREAK);
				}
				break;
			case 5:
				{
				setState(115);
				act();
				}
				break;
			case 6:
				{
				setState(116);
				act();
				setState(117);
				match(T__11);
				setState(119);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==ID) {
					{
					setState(118);
					updatelist();
					}
				}

				setState(121);
				match(T__12);
				}
				break;
			case 7:
				{
				setState(123);
				match(T__13);
				setState(124);
				process(0);
				setState(125);
				match(T__14);
				}
				break;
			case 8:
				{
				setState(127);
				match(T__15);
				setState(128);
				proclist();
				setState(129);
				match(T__14);
				}
				break;
			case 9:
				{
				setState(131);
				match(T__16);
				setState(132);
				proclist();
				setState(133);
				match(T__14);
				}
				break;
			case 10:
				{
				setState(135);
				match(T__17);
				setState(136);
				proclist();
				setState(137);
				match(T__14);
				}
				break;
			case 11:
				{
				setState(139);
				match(T__18);
				setState(140);
				bexpr(0);
				setState(141);
				match(T__1);
				setState(142);
				process(4);
				}
				break;
			case 12:
				{
				setState(144);
				match(T__19);
				setState(145);
				bexpr(0);
				setState(146);
				match(T__1);
				setState(147);
				process(0);
				setState(148);
				match(T__20);
				setState(149);
				process(3);
				}
				break;
			case 13:
				{
				setState(151);
				match(T__21);
				setState(152);
				bexpr(0);
				setState(153);
				match(T__1);
				setState(154);
				process(2);
				}
				break;
			case 14:
				{
				setState(156);
				match(T__16);
				setState(157);
				process(0);
				setState(158);
				match(T__14);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(167);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,12,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new ProcessContext(_parentctx, _parentState);
					pushNewRecursionContext(_localctx, _startState, RULE_process);
					setState(162);
					if (!(precpred(_ctx, 8))) throw new FailedPredicateException(this, "precpred(_ctx, 8)");
					setState(163);
					match(T__8);
					setState(164);
					process(9);
					}
					} 
				}
				setState(169);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,12,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class ProclistContext extends ParserRuleContext {
		public List<ProcessContext> process() {
			return getRuleContexts(ProcessContext.class);
		}
		public ProcessContext process(int i) {
			return getRuleContext(ProcessContext.class,i);
		}
		public ProclistContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_proclist; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitProclist(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ProclistContext proclist() throws RecognitionException {
		ProclistContext _localctx = new ProclistContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_proclist);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(170);
			match(T__22);
			setState(171);
			process(0);
			setState(176);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__22) {
				{
				{
				setState(172);
				match(T__22);
				setState(173);
				process(0);
				}
				}
				setState(178);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class UpdatelistContext extends ParserRuleContext {
		public List<UpdateContext> update() {
			return getRuleContexts(UpdateContext.class);
		}
		public UpdateContext update(int i) {
			return getRuleContext(UpdateContext.class,i);
		}
		public UpdatelistContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_updatelist; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitUpdatelist(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UpdatelistContext updatelist() throws RecognitionException {
		UpdatelistContext _localctx = new UpdatelistContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_updatelist);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(179);
			update();
			setState(184);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__23) {
				{
				{
				setState(180);
				match(T__23);
				setState(181);
				update();
				}
				}
				setState(186);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class UpdateContext extends ParserRuleContext {
		public VnameContext vname() {
			return getRuleContext(VnameContext.class,0);
		}
		public ExprContext expr() {
			return getRuleContext(ExprContext.class,0);
		}
		public UpdateContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_update; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitUpdate(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UpdateContext update() throws RecognitionException {
		UpdateContext _localctx = new UpdateContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_update);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(187);
			vname();
			setState(188);
			match(T__9);
			setState(189);
			expr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class TformContext extends ParserRuleContext {
		public BexprContext bexpr() {
			return getRuleContext(BexprContext.class,0);
		}
		public List<TformContext> tform() {
			return getRuleContexts(TformContext.class);
		}
		public TformContext tform(int i) {
			return getRuleContext(TformContext.class,i);
		}
		public TerminalNode APATH() { return getToken(MudsParser.APATH, 0); }
		public TerminalNode EPATH() { return getToken(MudsParser.EPATH, 0); }
		public TerminalNode GLOB() { return getToken(MudsParser.GLOB, 0); }
		public TerminalNode EVENT() { return getToken(MudsParser.EVENT, 0); }
		public TerminalNode NEXT() { return getToken(MudsParser.NEXT, 0); }
		public TerminalNode NOT() { return getToken(MudsParser.NOT, 0); }
		public TerminalNode UNTIL() { return getToken(MudsParser.UNTIL, 0); }
		public TformContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_tform; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof MudsVisitor ) return ((MudsVisitor<? extends T>)visitor).visitTform(this);
			else return visitor.visitChildren(this);
		}
	}

	public final TformContext tform() throws RecognitionException {
		return tform(0);
	}

	private TformContext tform(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		TformContext _localctx = new TformContext(_ctx, _parentState);
		TformContext _prevctx = _localctx;
		int _startState = 22;
		enterRecursionRule(_localctx, 22, RULE_tform, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(209);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,15,_ctx) ) {
			case 1:
				{
				setState(192);
				bexpr(0);
				}
				break;
			case 2:
				{
				setState(193);
				match(T__0);
				setState(194);
				tform(0);
				setState(195);
				match(T__1);
				}
				break;
			case 3:
				{
				setState(197);
				match(APATH);
				setState(198);
				tform(7);
				}
				break;
			case 4:
				{
				setState(199);
				match(EPATH);
				setState(200);
				tform(6);
				}
				break;
			case 5:
				{
				setState(201);
				match(GLOB);
				setState(202);
				tform(5);
				}
				break;
			case 6:
				{
				setState(203);
				match(EVENT);
				setState(204);
				tform(4);
				}
				break;
			case 7:
				{
				setState(205);
				match(NEXT);
				setState(206);
				tform(2);
				}
				break;
			case 8:
				{
				setState(207);
				match(NOT);
				setState(208);
				tform(1);
				}
				break;
			}
			_ctx.stop = _input.LT(-1);
			setState(222);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,17,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					setState(220);
					_errHandler.sync(this);
					switch ( getInterpreter().adaptivePredict(_input,16,_ctx) ) {
					case 1:
						{
						_localctx = new TformContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_tform);
						setState(211);
						if (!(precpred(_ctx, 10))) throw new FailedPredicateException(this, "precpred(_ctx, 10)");
						setState(212);
						match(T__24);
						setState(213);
						tform(11);
						}
						break;
					case 2:
						{
						_localctx = new TformContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_tform);
						setState(214);
						if (!(precpred(_ctx, 9))) throw new FailedPredicateException(this, "precpred(_ctx, 9)");
						setState(215);
						match(T__25);
						setState(216);
						tform(10);
						}
						break;
					case 3:
						{
						_localctx = new TformContext(_parentctx, _parentState);
						pushNewRecursionContext(_localctx, _startState, RULE_tform);
						setState(217);
						if (!(precpred(_ctx, 3))) throw new FailedPredicateException(this, "precpred(_ctx, 3)");
						setState(218);
						match(UNTIL);
						setState(219);
						tform(4);
						}
						break;
					}
					} 
				}
				setState(224);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,17,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 0:
			return iexpr_sempred((IexprContext)_localctx, predIndex);
		case 1:
			return bexpr_sempred((BexprContext)_localctx, predIndex);
		case 7:
			return process_sempred((ProcessContext)_localctx, predIndex);
		case 11:
			return tform_sempred((TformContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean iexpr_sempred(IexprContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 3);
		case 1:
			return precpred(_ctx, 2);
		}
		return true;
	}
	private boolean bexpr_sempred(BexprContext _localctx, int predIndex) {
		switch (predIndex) {
		case 2:
			return precpred(_ctx, 4);
		case 3:
			return precpred(_ctx, 3);
		}
		return true;
	}
	private boolean process_sempred(ProcessContext _localctx, int predIndex) {
		switch (predIndex) {
		case 4:
			return precpred(_ctx, 8);
		}
		return true;
	}
	private boolean tform_sempred(TformContext _localctx, int predIndex) {
		switch (predIndex) {
		case 5:
			return precpred(_ctx, 10);
		case 6:
			return precpred(_ctx, 9);
		case 7:
			return precpred(_ctx, 3);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\60\u00e4\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\3\2\3\2\3\2\3\2\3\2\3\2\3\2\5\2\"\n\2\3\2\3\2\3"+
		"\2\3\2\3\2\3\2\7\2*\n\2\f\2\16\2-\13\2\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3"+
		"\3\3\3\3\3\3\3\3\3\3\3\3\5\3=\n\3\3\3\3\3\3\3\3\3\3\3\3\3\7\3E\n\3\f\3"+
		"\16\3H\13\3\3\4\3\4\5\4L\n\4\3\5\3\5\3\6\3\6\3\7\3\7\3\b\3\b\3\b\3\b\3"+
		"\b\3\b\3\b\3\b\5\b\\\n\b\3\b\3\b\3\b\3\b\3\b\3\b\5\bd\n\b\3\b\3\b\3\b"+
		"\3\b\3\b\3\b\3\b\3\b\3\b\3\b\5\bp\n\b\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t"+
		"\5\tz\n\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t"+
		"\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3"+
		"\t\3\t\3\t\3\t\3\t\3\t\3\t\5\t\u00a3\n\t\3\t\3\t\3\t\7\t\u00a8\n\t\f\t"+
		"\16\t\u00ab\13\t\3\n\3\n\3\n\3\n\7\n\u00b1\n\n\f\n\16\n\u00b4\13\n\3\13"+
		"\3\13\3\13\7\13\u00b9\n\13\f\13\16\13\u00bc\13\13\3\f\3\f\3\f\3\f\3\r"+
		"\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\5"+
		"\r\u00d4\n\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\7\r\u00df\n\r\f\r\16"+
		"\r\u00e2\13\r\3\r\2\6\2\4\20\30\16\2\4\6\b\n\f\16\20\22\24\26\30\2\4\3"+
		"\2\7\b\4\2\t\t,,\2\u0104\2!\3\2\2\2\4<\3\2\2\2\6K\3\2\2\2\bM\3\2\2\2\n"+
		"O\3\2\2\2\fQ\3\2\2\2\16o\3\2\2\2\20\u00a2\3\2\2\2\22\u00ac\3\2\2\2\24"+
		"\u00b5\3\2\2\2\26\u00bd\3\2\2\2\30\u00d3\3\2\2\2\32\33\b\2\1\2\33\"\7"+
		"-\2\2\34\"\5\b\5\2\35\36\7\3\2\2\36\37\5\2\2\2\37 \7\4\2\2 \"\3\2\2\2"+
		"!\32\3\2\2\2!\34\3\2\2\2!\35\3\2\2\2\"+\3\2\2\2#$\f\5\2\2$%\7$\2\2%*\5"+
		"\2\2\6&\'\f\4\2\2\'(\7#\2\2(*\5\2\2\5)#\3\2\2\2)&\3\2\2\2*-\3\2\2\2+)"+
		"\3\2\2\2+,\3\2\2\2,\3\3\2\2\2-+\3\2\2\2./\b\3\1\2/=\7 \2\2\60=\7!\2\2"+
		"\61=\5\b\5\2\62\63\7\'\2\2\63=\5\4\3\7\64\65\7\3\2\2\65\66\5\4\3\2\66"+
		"\67\7\4\2\2\67=\3\2\2\289\5\2\2\29:\7\"\2\2:;\5\2\2\2;=\3\2\2\2<.\3\2"+
		"\2\2<\60\3\2\2\2<\61\3\2\2\2<\62\3\2\2\2<\64\3\2\2\2<8\3\2\2\2=F\3\2\2"+
		"\2>?\f\6\2\2?@\7\5\2\2@E\5\4\3\7AB\f\5\2\2BC\7\6\2\2CE\5\4\3\6D>\3\2\2"+
		"\2DA\3\2\2\2EH\3\2\2\2FD\3\2\2\2FG\3\2\2\2G\5\3\2\2\2HF\3\2\2\2IL\5\2"+
		"\2\2JL\5\4\3\2KI\3\2\2\2KJ\3\2\2\2L\7\3\2\2\2MN\7,\2\2N\t\3\2\2\2OP\t"+
		"\2\2\2P\13\3\2\2\2QR\t\3\2\2R\r\3\2\2\2ST\7\n\2\2TU\7,\2\2UV\7\13\2\2"+
		"Vp\5\16\b\2WX\7\7\2\2X[\7,\2\2YZ\7\f\2\2Z\\\5\2\2\2[Y\3\2\2\2[\\\3\2\2"+
		"\2\\]\3\2\2\2]^\7\13\2\2^p\5\16\b\2_`\7\b\2\2`c\7,\2\2ab\7\f\2\2bd\5\4"+
		"\3\2ca\3\2\2\2cd\3\2\2\2de\3\2\2\2ef\7\13\2\2fp\5\16\b\2gh\7\r\2\2hi\7"+
		",\2\2ij\7\f\2\2jk\5\30\r\2kl\7\13\2\2lm\5\16\b\2mp\3\2\2\2np\5\20\t\2"+
		"oS\3\2\2\2oW\3\2\2\2o_\3\2\2\2og\3\2\2\2on\3\2\2\2p\17\3\2\2\2q\u00a3"+
		"\b\t\1\2r\u00a3\7\37\2\2s\u00a3\7\36\2\2t\u00a3\7\35\2\2u\u00a3\5\f\7"+
		"\2vw\5\f\7\2wy\7\16\2\2xz\5\24\13\2yx\3\2\2\2yz\3\2\2\2z{\3\2\2\2{|\7"+
		"\17\2\2|\u00a3\3\2\2\2}~\7\20\2\2~\177\5\20\t\2\177\u0080\7\21\2\2\u0080"+
		"\u00a3\3\2\2\2\u0081\u0082\7\22\2\2\u0082\u0083\5\22\n\2\u0083\u0084\7"+
		"\21\2\2\u0084\u00a3\3\2\2\2\u0085\u0086\7\23\2\2\u0086\u0087\5\22\n\2"+
		"\u0087\u0088\7\21\2\2\u0088\u00a3\3\2\2\2\u0089\u008a\7\24\2\2\u008a\u008b"+
		"\5\22\n\2\u008b\u008c\7\21\2\2\u008c\u00a3\3\2\2\2\u008d\u008e\7\25\2"+
		"\2\u008e\u008f\5\4\3\2\u008f\u0090\7\4\2\2\u0090\u0091\5\20\t\6\u0091"+
		"\u00a3\3\2\2\2\u0092\u0093\7\26\2\2\u0093\u0094\5\4\3\2\u0094\u0095\7"+
		"\4\2\2\u0095\u0096\5\20\t\2\u0096\u0097\7\27\2\2\u0097\u0098\5\20\t\5"+
		"\u0098\u00a3\3\2\2\2\u0099\u009a\7\30\2\2\u009a\u009b\5\4\3\2\u009b\u009c"+
		"\7\4\2\2\u009c\u009d\5\20\t\4\u009d\u00a3\3\2\2\2\u009e\u009f\7\23\2\2"+
		"\u009f\u00a0\5\20\t\2\u00a0\u00a1\7\21\2\2\u00a1\u00a3\3\2\2\2\u00a2q"+
		"\3\2\2\2\u00a2r\3\2\2\2\u00a2s\3\2\2\2\u00a2t\3\2\2\2\u00a2u\3\2\2\2\u00a2"+
		"v\3\2\2\2\u00a2}\3\2\2\2\u00a2\u0081\3\2\2\2\u00a2\u0085\3\2\2\2\u00a2"+
		"\u0089\3\2\2\2\u00a2\u008d\3\2\2\2\u00a2\u0092\3\2\2\2\u00a2\u0099\3\2"+
		"\2\2\u00a2\u009e\3\2\2\2\u00a3\u00a9\3\2\2\2\u00a4\u00a5\f\n\2\2\u00a5"+
		"\u00a6\7\13\2\2\u00a6\u00a8\5\20\t\13\u00a7\u00a4\3\2\2\2\u00a8\u00ab"+
		"\3\2\2\2\u00a9\u00a7\3\2\2\2\u00a9\u00aa\3\2\2\2\u00aa\21\3\2\2\2\u00ab"+
		"\u00a9\3\2\2\2\u00ac\u00ad\7\31\2\2\u00ad\u00b2\5\20\t\2\u00ae\u00af\7"+
		"\31\2\2\u00af\u00b1\5\20\t\2\u00b0\u00ae\3\2\2\2\u00b1\u00b4\3\2\2\2\u00b2"+
		"\u00b0\3\2\2\2\u00b2\u00b3\3\2\2\2\u00b3\23\3\2\2\2\u00b4\u00b2\3\2\2"+
		"\2\u00b5\u00ba\5\26\f\2\u00b6\u00b7\7\32\2\2\u00b7\u00b9\5\26\f\2\u00b8"+
		"\u00b6\3\2\2\2\u00b9\u00bc\3\2\2\2\u00ba\u00b8\3\2\2\2\u00ba\u00bb\3\2"+
		"\2\2\u00bb\25\3\2\2\2\u00bc\u00ba\3\2\2\2\u00bd\u00be\5\b\5\2\u00be\u00bf"+
		"\7\f\2\2\u00bf\u00c0\5\6\4\2\u00c0\27\3\2\2\2\u00c1\u00c2\b\r\1\2\u00c2"+
		"\u00d4\5\4\3\2\u00c3\u00c4\7\3\2\2\u00c4\u00c5\5\30\r\2\u00c5\u00c6\7"+
		"\4\2\2\u00c6\u00d4\3\2\2\2\u00c7\u00c8\7&\2\2\u00c8\u00d4\5\30\r\t\u00c9"+
		"\u00ca\7%\2\2\u00ca\u00d4\5\30\r\b\u00cb\u00cc\7(\2\2\u00cc\u00d4\5\30"+
		"\r\7\u00cd\u00ce\7)\2\2\u00ce\u00d4\5\30\r\6\u00cf\u00d0\7+\2\2\u00d0"+
		"\u00d4\5\30\r\4\u00d1\u00d2\7\'\2\2\u00d2\u00d4\5\30\r\3\u00d3\u00c1\3"+
		"\2\2\2\u00d3\u00c3\3\2\2\2\u00d3\u00c7\3\2\2\2\u00d3\u00c9\3\2\2\2\u00d3"+
		"\u00cb\3\2\2\2\u00d3\u00cd\3\2\2\2\u00d3\u00cf\3\2\2\2\u00d3\u00d1\3\2"+
		"\2\2\u00d4\u00e0\3\2\2\2\u00d5\u00d6\f\f\2\2\u00d6\u00d7\7\33\2\2\u00d7"+
		"\u00df\5\30\r\r\u00d8\u00d9\f\13\2\2\u00d9\u00da\7\34\2\2\u00da\u00df"+
		"\5\30\r\f\u00db\u00dc\f\5\2\2\u00dc\u00dd\7*\2\2\u00dd\u00df\5\30\r\6"+
		"\u00de\u00d5\3\2\2\2\u00de\u00d8\3\2\2\2\u00de\u00db\3\2\2\2\u00df\u00e2"+
		"\3\2\2\2\u00e0\u00de\3\2\2\2\u00e0\u00e1\3\2\2\2\u00e1\31\3\2\2\2\u00e2"+
		"\u00e0\3\2\2\2\24!)+<DFK[coy\u00a2\u00a9\u00b2\u00ba\u00d3\u00de\u00e0";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}