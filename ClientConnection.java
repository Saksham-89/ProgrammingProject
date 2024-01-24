package ProgrammingProject;



import java.io.IOException;
import java.net.Socket;
import java.util.Arrays;
import ss.week7.src.ss.networking.SocketConnection;

/**
 * The `ClientConnection` class represents a TCP connection to a server, extending the `SocketConnection` class.
 * It provides methods for sending various commands to the server and handling incoming messages.
 */
public class ClientConnection extends SocketConnection {
    private final Client client;

    /**
     * Make a new TCP connection to the given host and port.
     * The receiving thread is not started yet. Call start on the returned SocketConnection to start receiving messages.
     *
     * @param socket the socket to connect to
     * @throws IOException if the connection cannot be made or there was some other I/O problem
     */
    public ClientConnection(Socket socket, Client client) throws IOException {
        super(socket);
        this.client = client;
        start();
    }

    /**
     * Initiate a handshake with the server by sending Hello.
     */
    public void sendHello() {
        String encoded = Protocol.HELLO + Protocol.SEPARATOR + client.getDescription();
        sendMessage(encoded);
    }

    /**
     * Send a move to the server.
     * @param move the move that needs to be made
     */
    //@ requires 0 <= move && move <= 59;
    public void sendMove(int move) {
        String encoded = Protocol.MOVE + Protocol.SEPARATOR + move;
        sendMessage(encoded);
    }

    /**
     * Send a username to log in to the server.
     * @param username the username that should be sent
     */
    //@ requires username != null && !username.contains(Protocol.SEPARATOR);
    public void sendUsername(String username) {
        String encoded = Protocol.LOGIN + Protocol.SEPARATOR + username;
        sendMessage(encoded);
    }

    /**
     * Send the queue command, indicating that the client wants to join/leave the queue.
     */
    public void sendQueue() {
        String encoded = Protocol.QUEUE;
        sendMessage(encoded);
    }

    /**
     * Send the list command to request a list of clients who are currently logged into the server.
     */
    public void sendList() {
        String encoded = Protocol.LIST;
        sendMessage(encoded);
    }

    /**
     * Send an error
     */
    public void sendError(Exception e) {
        String encoded = Protocol.ERROR + Protocol.SEPARATOR + e.getMessage();
        sendMessage(encoded);
    }

    /**
     * Handles a message received from the connection.
     *
     * @param message the message received from the connection
     */
    @Override
    protected void handleMessage(String message) {
        if (message == null) return;
        String[] args = message.split(Protocol.SEPARATOR);
        switch (args[0]) {
            case Protocol.HELLO:
                if (args.length < 2) {
                    sendError(new InvalidCommandArgumentsException());
                    break;
                }
                client.receiveHello();
                break;
            case Protocol.LOGIN:
                client.receiveLogin();
                break;
            case Protocol.ALREADYLOGGEDIN:
                client.receiveAlreadyLoggedIn();
                break;
            case Protocol.LIST:
                if (args.length < 2) {
                    sendError(new InvalidCommandArgumentsException());
                    break;
                }
                client.receiveList(Arrays.copyOfRange(args, 1, args.length));
                break;
            case Protocol.NEWGAME:
                if (args.length != 3) {
                    sendError(new InvalidCommandArgumentsException());
                    break;
                }
                client.receiveNewGame(args[1], args[2]);
                break;
            case Protocol.MOVE:
                if (args.length != 2) {
                    sendError(new InvalidCommandArgumentsException());
                    break;
                }
                client.receiveMove(Integer.parseInt(args[1]));
                break;
            case Protocol.GAMEOVER:
                if (args.length < 2) {
                    sendError(new InvalidCommandArgumentsException());
                    break;
                }
                else if (args.length == 2) {
                    client.receiveGameOver(args[1], null);
                } else {
                    client.receiveGameOver(args[1], args[2]);
                }
                break;
            default:
                sendError(new InvalidCommandException());
        }
    }

    /**
     * Handles a disconnect from the connection, i.e., when the connection is closed.
     */
    @Override
    protected void handleDisconnect() {
        client.handleDisconnect();
        close();
    }

    public void close() {
        super.close();
    }
}
