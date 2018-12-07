import java.util.concurrent.TimeUnit;

public class MudsMain {

	
	public static void main(String[] args) {
		
		AbstractChecker checker = new Part1();
		
		for (String arg : args) {
			System.out.println("Running: "+arg);
			checker.run(arg);
			try {
				TimeUnit.MILLISECONDS.sleep(10);
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			System.out.println("########################################");
		}
		
		/*
		if( args.length == 1)
			checker.run(args[0]);
		else
			System.err.println("Provide a filename as first argument."); */
	}
}


	