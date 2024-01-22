package ProgrammingProject;

import ss.week7.src.ss.networking.SocketConnection;

import java.io.IOException;
import java.net.Socket;

public class ClientConnection extends SocketConnection {

    private Client client;

    public ClientConnection(Socket socket, Client client) throws IOException {
        super(socket);
        this.client = client;
    }

    @Override
    protected void handleMessage(String message) throws IOException {
        String[] parts = message.split(" ");
        String command = parts[0];

        switch (command) {
            case "MOVE":
                if (parts.length > 1) {
                    int move = Integer.parseInt(parts[1]);
                    client.receiveMove(move);
                }
                break;
            case "LIST":
                if (parts.length > 1) {
                    String[] list = parts[1].split(",");
                    client.receiveList(list);
                }
                break;
            case "NEWGAME":
                client.receiveNewGame();
                break;
            case "GAMEOVER":
                if (parts.length > 2) {
                    String reason = parts[1];
                    String winner = parts[2];
                    client.receiveGameOver(reason, winner);
                }
                break;
            // Add more cases as needed for other commands

            default:
                // Unknown command, ignore or handle as needed
                break;
        }
    }

    @Override
    protected void handleDisconnect() {
        // Notify the client about the disconnection
        client.handleDisconnect();
    }

    // Additional methods specific to ClientConnection

    public void sendMove(int move) throws IOException {
        // Assuming you have a method to send messages to the server
        sendMessage("MOVE " + move);
    }

    public void sendUsername(String username) throws IOException {
        // Assuming you have a method to send messages to the server
        sendMessage("USERNAME " + username);
    }

    public void sendQueue() throws IOException {
        // Assuming you have a method to send messages to the server
        sendMessage("QUEUE");
    }

    public void sendList() throws IOException {
        // Assuming you have a method to send messages to the server
        sendMessage("LIST");
    }

    // Other methods as needed
}
