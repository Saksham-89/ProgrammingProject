package ProgrammingProject;

public class InvalidCommandException extends Exception {

    public InvalidCommandException() {
        super("The command that was sent is invalid.");
    }
}
