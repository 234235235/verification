

public class MudsMain {

	
	public static void main(String[] args) {
		
		AbstractChecker checker = new Part3();
		if( args.length == 1)
			checker.run(args[0]);
		else
			System.err.println("Provide a filename as first argument.");
	}
}


	