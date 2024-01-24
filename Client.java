package ProgrammingProject;

import java.io.IOException;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

/**
 * The Client class represents a client in a network application.
 * It manages the communication with a server using a {@link ClientConnection}.
 * The client can send and receive various messages and notifies registered listeners accordingly.
 * This class also provides methods to handle disconnection and manage listeners.
 */
public class Client {
    private final ClientConnection clientConnection;
    private final List<ClientListener> listeners = new ArrayList<>();
    private static final String DESCRIPTION = "Matt's client";

    /**
     * Creates a new Client instance with the specified socket.
     *
     * @param socket The socket used for communication with the server.
     * @throws IOException If an I/O error occurs while creating the client.
     */
    public Client(Socket socket) throws IOException {
        clientConnection = new ClientConnection(socket, this);
    }

    /**
     * Notifies all registered listeners about receiving a "hello" message.
     */
    public void receiveHello() {
        for (ClientListener listener : listeners) {
            listener.hello();
        }
    }

    /**
     * Notifies all registered listeners about receiving a "login" message.
     */
    public void receiveLogin() {
        for (ClientListener listener : listeners) {
            listener.login();
        }
    }

    /**
     * Notifies all registered listeners about receiving an "already logged in" message.
     */
    public void receiveAlreadyLoggedIn() {
        for (ClientListener listener : listeners) {
            listener.alreadyLoggedIn();
        }
    }

    /**
     * Notifies all registered listeners about receiving a move message.
     *
     * @param move The move received from the server.
     */
    public void receiveMove(int move) {
        for (ClientListener listener : listeners) {
            listener.move(move);
        }
    }

    /**
     * Notifies all registered listeners about receiving a list message.
     *
     * @param list The list received from the server.
     */
    public void receiveList(String[] list) {
        for (ClientListener listener : listeners) {
            listener.list(list);
        }
    }

    /**
     * Notifies all registered listeners about starting a new game.
     *
     * @param player1 The username of player 1.
     * @param player2 The username of player 2.
     */
    public void receiveNewGame(String player1, String player2) {
        for (ClientListener listener : listeners) {
            listener.newGame(player1, player2);
        }
    }

    /**
     * Notifies all registered listeners about the game being over.
     *
     * @param reason The reason for the game's end.
     * @param winner The username of the winner.
     */
    public void receiveGameOver(String reason, String winner) {
        for (ClientListener listener : listeners) {
            listener.gameOver(reason, winner);
        }
    }

    /**
     * Sends a "hello" message to the server.
     */
    public void sendHello() {
        clientConnection.sendHello();
    }

    /**
     * Sends a move message to the server.
     *
     * @param move The move to be sent to the server.
     */
    public void sendMove(int move) {
        clientConnection.sendMove(move);
    }

    /**
     * Sends a username to the server.
     *
     * @param username The username to be sent to the server.
     */
    public void sendUsername(String username) {
        clientConnection.sendUsername(username);
    }

    /**
     * Sends a queue message to the server.
     */
    public void sendQueue() {
        clientConnection.sendQueue();
    }

    /**
     * Sends a list message request to the server.
     */
    public void sendList() {
        clientConnection.sendList();
    }

    /**
     * Adds a listener to be notified of events from the server.
     *
     * @param listener The listener to be added.
     */
    public synchronized void addListener(ClientListener listener) {
        listeners.add(listener);
    }

    /**
     * Removes a listener from the list of listeners.
     *
     * @param listener The listener to be removed.
     */
    public synchronized void removeListener(ClientListener listener) {
        listeners.remove(listener);
    }

    /**
     * Notifies all listeners about the connection being lost.
     */
    public void handleDisconnect() {
        for (ClientListener cl : listeners) {
            cl.connectionLost();
        }
    }

    /**
     * Closes the client connection.
     */
    public void close() {
        clientConnection.close();
    }

    /**
     * Gets the description of the client.
     *
     * @return The client description.
     */
    //@ ensures \result == this.DESCRIPTION;
    //@ pure
    public String getDescription() {
        return DESCRIPTION;
    }
}
