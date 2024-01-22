package ProgrammingProject;

import java.net.Socket;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class Client {
    private ClientConnection clientConnection;
    private List<ClientListener> listeners;

    public Client(Socket socket) {
        try {
            clientConnection = new ClientConnection(socket, this);
            listeners = new ArrayList<>();
            // Add listeners if needed
        } catch (IOException e) {
            e.printStackTrace();
            // Handle the exception as needed
        }
    }

    public void addListener(ClientListener listener) {
        listeners.add(listener);
    }

    public void removeListener(ClientListener listener) {
        listeners.remove(listener);
    }

    public void start() {
        clientConnection.start();
    }

    public void receiveMove(int move) {
        // Notify listeners about the received move
        for (ClientListener listener : listeners) {
            listener.move(move);
        }
    }

    public void receiveList(String[] list) {
        // Notify listeners about the received list
        for (ClientListener listener : listeners) {
            listener.list(list);
        }
    }

    public void receiveNewGame() {
        // Notify listeners about the start of a new game
        for (ClientListener listener : listeners) {
            listener.newGame();
        }
    }

    public void receiveGameOver(String reason, String winner) {
        // Notify listeners about the game over event
        for (ClientListener listener : listeners) {
            listener.gameOver(reason, winner);
        }
    }

    public void sendMove(int move) {
        try {
            clientConnection.sendMove(move);
        } catch (IOException e) {
            e.printStackTrace();
            // Handle the exception as needed
        }
    }

    public void sendUsername(String username) {
        try {
            clientConnection.sendUsername(username);
        } catch (IOException e) {
            e.printStackTrace();
            // Handle the exception as needed
        }
    }

    public void sendQueue() {
        try {
            clientConnection.sendQueue();
        } catch (IOException e) {
            e.printStackTrace();
            // Handle the exception as needed
        }
    }

    public void sendList() {
        try {
            clientConnection.sendList();
        } catch (IOException e) {
            e.printStackTrace();
            // Handle the exception as needed
        }
    }

    public void handleDisconnect() {

    }

    public void close() {
        // Close the client connection and perform any necessary cleanup
        clientConnection.close();
    }


    // Other methods as needed
}
