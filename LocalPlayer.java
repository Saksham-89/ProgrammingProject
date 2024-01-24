package ProgrammingProject;


/**
 * Represents a local player in a Dots and Boxes game.
 * This class manages the local player's information and decisions during the game.
 */
public class LocalPlayer {

    private String name;

    /**
     * Constructs a LocalPlayer with a given name.
     *
     * @param name The name of the local player.
     */

    public LocalPlayer(String name){
        this.name = name;
    }

    /**
     * Retrieves the name of the local player.
     *
     * @return The name of the local player.
     */

    public String getName(){
        return name;
    }

    /**
     * Determines the next move for the local player in the Dots and Boxes game.
     * This method selects the first unfilled field on the board as the move.
     *
     * @param game The instance of DotsAndBoxesGame for which the move is being determined.
     * @return A Move object representing the chosen move, or null if no move is possible.
     */
    public Move determineMove(DotsAndBoxesGame game) {

        for (int field = 0; field < Board.DIM * Board.DIM; field++) {
            if (!game.getBoard().isFilled(field)) {
                return new Move(field);
            }
        }

        return null;
    }
    /**
     * Returns a string representation of the local player.
     *
     * @return A string containing the type and name of the local player.
     */



    public String toString(){
        return "Local Player: " + name;
    }
}
