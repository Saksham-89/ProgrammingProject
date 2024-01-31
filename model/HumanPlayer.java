package ProgrammingProject.model;

import java.util.Scanner;
/**
 * Represents a human player in the Dots and Boxes game.
 * This class allows for human input to determine moves during the game.
 */
public class HumanPlayer extends AbstractPlayer {

    private final Line line;
    /**
     * Constructs a HumanPlayer with a specified name and line color.
     *
     * @param name The name of the player.
     * @param line The line color associated with the player.
     */
    /*@
      @ requires name != null && (line == Line.BLUE || line == Line.RED);
      @ ensures getName().equals(name) && this.line == line;
      @*/
    public HumanPlayer(String name, Line line){
        super(name);
        this.line = line;
    }
    /**
     * Prompts the human player to enter a move and validates it.
     * The move must be entered in the format "start-end" where start and end are integers.
     *
     * @param game The current state of the Dots and Boxes game.
     * @return A valid DotsAndBoxesMove based on the player's input, or null if the input is invalid.
     */
    /*@
      @ requires game != null;
      @ ensures \result == null || game.validMove(\result);
      @ signals (NumberFormatException) false;
      @*/
    @Override
    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game) {
        Scanner input = new Scanner(System.in);
        try {
            System.out.print("Enter your move: ");
            String move = input.nextLine();
            String[] splitMove = move.split("-");

            if (splitMove.length != 2) {
                System.out.println("Invalid move format. Please input as 'start-end'.");
                return null;
            }

            int start = Integer.parseInt(splitMove[0].trim());
            int end = Integer.parseInt(splitMove[1].trim());

            DotsAndBoxesMove newMove = new DotsAndBoxesMove(line, start, end);

            if (!game.validMove(newMove)) {
                System.out.println("Invalid move. Please try again.");
                return null;
            }

            return newMove;
        } catch (NumberFormatException e) {
            System.out.println("Invalid number format. Please input integers in 'start-end' format.");
            return null;
        }
    }

}
