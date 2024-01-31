package ProgrammingProject.model;
/**
 * Represents an abstract player in the Dots and Boxes game.
 * This class provides a common structure for all types of players, defining the basic functionality that
 * all players must have, including a method to determine the next move based on the current game state.
 */
public abstract class AbstractPlayer implements Player{
    private final String name;


    /**
     * Constructs an AbstractPlayer with the specified name.
     *
     * @param name The name of the player. This parameter must not be null.
     * @throws NullPointerException if the name is null, ensuring that every player has a valid name.
     */
    /*@ requires name != null;
        ensures getName().equals(name);
    @*/
    public AbstractPlayer(String name) {
        this.name = name;
    }

    /**
     * Gets the name of the player.
     *
     * @return The name of this player, which is never null.
     */
    //@ pure
    public String getName() {
        return name;
    }

    /**
     * Determines the next move for the player in the current game state.
     * This method is abstract and should be implemented by subclasses to define specific move logic,
     * taking into consideration the game's rules and the current situation on the board.
     *
     * @param game The current state of the Dots and Boxes game, which must not be null and the game should not be over.
     * @return The move determined by the player, which must be a valid move within the context of the game.
     */
    public abstract DotsAndBoxesMove determineMove(DotsAndBoxesGame game);

    /**
     * Returns a string representation of the player, primarily for debugging purposes.
     * This representation includes the player's name, making it easier to identify the player in logs or output.
     *
     * @return A string that represents this player, including the name.
     */
    @Override
    public String toString() {
        return "Player " + name;
    }
}
