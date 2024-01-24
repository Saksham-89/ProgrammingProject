package ProgrammingProject;

/**
 * Defines a set of methods that a client listener must implement to receive notifications from a client.
 */
public interface ClientListener {

    /**
     * Called when a "hello" message is received from the server.
     */
    void hello();

    /**
     * Called when a "login" message is received from the server.
     */
    void login();

    /**
     * Called when an "already logged in" message is received from the server.
     */
    void alreadyLoggedIn();

    /**
     * Called when a move message is received from the server.
     *
     * @param move The move received from the server.
     */
    void move(int move);

    /**
     * Called when a list message is received from the server.
     *
     * @param list The list received from the server.
     */
    void list(String[] list);

    /**
     * Called when a new game is initiated on the server.
     *
     * @param player1 The username of player 1.
     * @param player2 The username of player 2.
     */
    void newGame(String player1, String player2);

    /**
     * Called when the game is over, providing the reason and the winner's username.
     *
     * @param reason The reason for the game's end.
     * @param winner The username of the winner.
     */
    void gameOver(String reason, String winner);

    /**
     * Called when the connection to the server is lost.
     */
    void connectionLost();
}
