

// ANTLR4 info
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Paths;
import org.antlr.v4.runtime.*;

import parser.*;
import mudschecker.LTS;
import mudschecker.ProgLTS;
import mudspg.*;

import java.nio.file.Path;

public abstract class AbstractChecker {

	/**
	 * An actual model checking procedure
	 * @param model
	 * @param tform
	 * @return
	 */
	public abstract boolean solve(LTS model, TFormula tform, int bound);
	
	/**
	 * generate a parser for a particular input stream (can be a file, or a string or something else)
	 * @param inputStream
	 * @return
	 */
	private static MudsParser getParser(CharStream inputStream) {
		MudsLexer lexer = new MudsLexer(inputStream);
		CommonTokenStream commonTokenStream = new CommonTokenStream(lexer);
		MudsParser parser = new MudsParser(commonTokenStream);
		
		return parser;
	}
	
	/**
	 * Generate a parser for a file located in the sample directory
	 * @param fname
	 * @return
	 * @throws IOException
	 */
	protected static MudsParser getParserFromSample(String fname) {
		BufferedReader reader;
		Path path = Paths.get("samples", fname);
		try {
			reader = new BufferedReader(new FileReader(path.toFile()));
		
			// ANTLR4 stuff
			CharStream inputStream = CharStreams.fromReader(reader);
			return getParser(inputStream);
		} catch( IOException e) {
			System.err.println("Cannot open file " + path);
			return null;
		}
	}
	
	protected static MudsParser getParser(String str) {
		return getParser(CharStreams.fromString(str));
	}

	/**
	 * Actual run of the model checker on a file.
	 * 1/ parse the file
	 * 2/ look for the properties and aggregate them (into a AND clause)
	 * 3/ call the implemented solve method
	 * @param fileName
	 */
	public void run(String fileName) {
		MudsParser parser = getParserFromSample(fileName);
		
		MudsParser.ProgContext ctx = parser.prog();
		MudsToPGVisitor visitor = new MudsToPGVisitor();
		
		Prog prog = visitor.visitProg(ctx);

		
		TFormula tform = null;
		for(TFormula prop: prog.properties) {
			if(tform == null)
				tform = prop;
			else
				tform = new TFormula.And(tform, prop);
		}
		
		if(tform == null) {
			System.err.println("No property to check, giving up.");
			return;
		}
		
		LTS model = new ProgLTS(prog);
		if( solve(model, tform, 1000000) ) {
			System.out.println("Model is finite and satifies property.");
		} else {
			System.out.println("Model doesn't satisfy property, or is too large to be analyzed.");
		}
	}
}
	