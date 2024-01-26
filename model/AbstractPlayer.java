package ProgrammingProject.model;
/**
 * Represents an abstract player in the Dots and Boxes game.
 * This class provides a common structure for all types of players.
 */
public abstract class AbstractPlayer implements Player{
    private final String name;


    /**
     * Constructs an AbstractPlayer with the specified name.
     *
     * @param name The name of the player. This parameter must not be null.
     * @throws NullPointerException if the name is null.
     */
    /*@ requires name != null;
        ensures getName() == name;
    @*/
    public AbstractPlayer(String name) {
        this.name = name;
    }

    /**
     * Gets the name of the player.
     *
     * @return The name of this player.
     */
    //@ pure
    public String getName() {
        return name;
    }

    /**
     * Determines the next move for the player in the current game.
     * This method is abstract and should be implemented by subclasses to define specific move logic.
     *
     * @param game The current state of the game.
     * @return The move determined by the player.
     */
    //@ requires !game.isGameover();
    //@ ensures game.isValidMove(\result);
    public abstract DotsAndBoxesMove determineMove(DotsAndBoxesGame game);

    /**
     * Returns a string representation of the player, including the player's name.
     *
     * @return A string that represents this player.
     */
    @Override
    public String toString() {
        return "Player " + name;
    }
}
