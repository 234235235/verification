


public class MudsMain {

	
	public static void main(String[] args) {
		AbstractChecker checker = new Part1();
		for (String arg : args) {
			System.out.println("Running: "+arg);
			checker.run(arg);
			System.out.println("###################################");
		}
		/*
		if( args.length == 1)
			checker.run(args[0]);
		else
			System.err.println("Provide a filename as first argument."); */
	}
}


	