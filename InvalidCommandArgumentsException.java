package ProgrammingProject;

public class InvalidCommandArgumentsException extends Exception {
    public InvalidCommandArgumentsException() {
        super("The amount of arguments for the command is invalid");
    }
}
