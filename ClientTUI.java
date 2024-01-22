package ProgrammingProject;

import ProgrammingProject.DotsAndBoxesGame;
import ProgrammingProject.Client;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.List;
import java.util.Scanner;

public class ClientTUI implements ClientListener {

    private Client client;
    private DotsAndBoxesGame game;

    public ClientTUI(Client client) {
        this.client = client;
        this.game = new DotsAndBoxesGame();
        client.addListener(this);
    }

    public static void main(String[] args) throws IOException {
        // Replace with your actual server address and port
        InetAddress serverAddress = askAddress();
        int serverPort = askPort();
        Socket socket = new Socket(serverAddress, serverPort);

        Client client = new Client(socket);
        ClientTUI clientTUI = new ClientTUI(client);
        clientTUI.runTUI();
    }

    public void runTUI() {
        String username = askUsername();
        client.sendUsername(username);

        boolean running = true;
        while (running) {
            System.out.println("1. Start New Game");
            System.out.println("2. Make Move");
            System.out.println("3. Exit");

            int choice = askChoice();

            switch (choice) {
                case 1:
                    client.sendQueue(); // Start a new game
                    break;
                case 2:
                    int move = askMove();
                    client.sendMove(move);
                    break;
                case 3:
                    running = false;
                    break;
                default:
                    System.out.println("Invalid choice. Please try again.");
                    break;
            }
        }
    }

    @Override
    public void move(int move) {
        // Handle the received move
        System.out.println("Received move: " + move);
    }

    @Override
    public void list(String[] list) {
        // Handle the received list
        System.out.println("Received list:");
        for (String item : list) {
            System.out.println(item);
        }
    }

    @Override
    public void newGame() {
        // Handle the start of a new game
        System.out.println("New game started!");
    }

    @Override
    public void gameOver(String reason, String winner) {
        System.out.println("Game over: " + reason + " Winner: " + winner);
    }


    private String askUsername() {
        System.out.print("Enter your username: ");
        Scanner scanner = new Scanner(System.in);
        return scanner.nextLine();
    }

    private static InetAddress askAddress() {
        Scanner scanner = new Scanner(System.in);
        System.out.print("Enter the server address: ");
        InetAddress serverAddress = null;

        // Keep asking until a valid address is provided
        while (serverAddress == null) {
            try {
                String addressStr = scanner.nextLine();
                serverAddress = InetAddress.getByName(addressStr);
            } catch (UnknownHostException e) {
                System.out.println("Invalid address. Please enter a valid server address.");
            }
        }

        return serverAddress;
    }

    private static int askPort() {
        Scanner scanner = new Scanner(System.in);
        System.out.print("Enter the server port: ");
        int serverPort = 0;

        // Keep asking until a valid port is provided
        while (serverPort <= 0 || serverPort > 65535) {
            try {
                serverPort = scanner.nextInt();
                if (serverPort <= 0 || serverPort > 65535) {
                    System.out.println("Invalid port. Port must be between 1 and 65535.");
                }
            } catch (Exception e) {
                System.out.println("Invalid input. Please enter a valid port number.");
                scanner.nextLine();
            }
        }

        return serverPort;
    }

    private int askChoice() {
        System.out.print("Enter your choice: ");
        Scanner scanner = new Scanner(System.in);
        return scanner.nextInt();
    }

    private int askMove() {
        Scanner scanner = new Scanner(System.in);
        List<Integer> validMoves = game.getValidMoves();

        // Display the current state of the game (if needed)
        System.out.println("Current game state:");
        System.out.println(game.getBoard().toString());

        // Display the valid moves
        System.out.println("Valid moves: " + validMoves);

        // Keep asking until a valid move is provided
        while (true) {
            System.out.print("Enter your move: ");

            try {
                int chosenMove = scanner.nextInt();

                if (validMoves.contains(chosenMove)) {
                    return chosenMove;
                } else {
                    System.out.println("Invalid move. Please enter a valid move from the list.");
                }
            } catch (Exception e) {
                System.out.println("Invalid input. Please enter a valid move from the list.");
                scanner.nextLine();
            }
        }
    }
}
