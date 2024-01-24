package ProgrammingProject;


import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Scanner;

/**
 * Text-based User Interface (TUI) for a Dots and Boxes game client.
 * Implements the {@link ClientListener} interface to receive notifications from the client.
 */
public class DotsAndBoxesTUI implements ClientListener {
    private Client client;
    private final Scanner scanner;
    private final Object lock = new Object();
    private boolean loginSuccessful = false;
    private static final String HELPMENU =
            """
                    === Command Menu ===
                    - move <int>: Send a move where the number is between 0 and 59.
                      Example: move 42

                    - queue: Join the queue. If already in the queue, leave it.

                    - list: Get the list of currently connected clients to the server.

                    - quit: Disconnect from the server and exit the program.

                    ====================
                    """;

    /**
     * The entry point of the DotsAndBoxesTUI application.
     *
     * @param args Command-line arguments (not used).
     */
    public static void main(String[] args) {
        DotsAndBoxesTUI tui = new DotsAndBoxesTUI();
        tui.runTUI();
    }

    private DotsAndBoxesTUI() {
        scanner = new Scanner(System.in);
    }

    /**
     * Runs the DotsAndBoxesTUI application.
     */
    private void runTUI() {
        InetAddress address = getValidAddress();
        int port = getValidPort();

        try (Socket socket = new Socket(address, port)) {
            client = new Client(socket);
            client.addListener(this);

            client.sendHello();

            synchronized (lock) {
                lock.wait();
            }

            System.out.println("A connection with the server is established");

            while (!loginSuccessful) {
                String username = getValidUsername();
                client.sendUsername(username);

                synchronized (lock) {
                    lock.wait();
                }
            }

            System.out.println("You can now freely enter commands. Hint: say 'help' to get a list of commands");
            while (true) {
                String input = scanner.nextLine();
                handleInput(input);
            }


        } catch (IOException e) {
            System.out.println("An I/O Exception occurred, shutting down.");
        } catch (InterruptedException ignored) {
        }
    }

    /**
     * Handles the user input and executes the corresponding command.
     *
     * @param input The user input.
     */
    private void handleInput(String input) {
        String[] args = input.split(" ");
        switch (args[0]) {
            case "move":
                if (args.length < 2) {
                    System.out.println("Please provide a move to play, separated by a space character");
                    break;
                }
                try {
                    int move = Integer.parseInt(args[1]);
                    if (move < 0 || move > 59) {
                        System.out.println("Please provide a valid move, between 0 and 59");
                        break;
                    }
                    client.sendMove(move);
                } catch (NumberFormatException e) {
                    System.out.println("Please provide a numerical move");
                }
                break;
            case "queue":
                client.sendQueue();
                break;
            case "list":
                client.sendList();
                break;
            case "help":
                printHelp();
                break;
            case "quit":
                client.close();
                break;
            default:
                System.out.println("That is an invalid command. Hint: say 'help' to get a list of commands");
        }
    }

    /**
     * Gets a valid server address from the user.
     *
     * @return The InetAddress representing the server address.
     */
    private InetAddress getValidAddress() {
        InetAddress address = null;
        do {
            System.out.print("Enter the server address: ");
            String input = scanner.nextLine().trim();
            try {
                address = InetAddress.getByName(input);
            } catch (UnknownHostException e) {
                System.out.println("Invalid address. Please enter a valid one.");
            }
        } while (address == null);

        return address;
    }

    /**
     * Gets a valid port number from the user.
     *
     * @return The valid port number.
     */
    private int getValidPort() {
        int port;
        do {
            System.out.print("Enter the port: ");
            while (!scanner.hasNextInt()) {
                System.out.println("Invalid input. Please enter a valid port number.");
                scanner.next();
            }
            port = scanner.nextInt();
            scanner.nextLine();
        } while (!isValidPort(port));
        return port;
    }

    /**
     * Checks if the provided port number is valid.
     *
     * @param port The port number to be checked.
     * @return True if the port number is valid, false otherwise.
     */
    private boolean isValidPort(int port) {
        return port > 0 && port <= 65535;
    }

    /**
     * Gets a valid username from the user.
     *
     * @return The valid username.
     */
    private String getValidUsername() {
        String username;
        do {
            System.out.print("Enter your username: ");
            username = scanner.nextLine().trim();

            if (username.isEmpty()) {
                System.out.println("Username cannot be empty.");
            } else if (username.contains(Protocol.SEPARATOR)) {
                System.out.println("Username cannot contain the separator character.");
            }
        } while (username.isEmpty() || username.contains(Protocol.SEPARATOR));

        return username;
    }

    /**
     * Prints the help menu.
     */
    private void printHelp() {
        System.out.println(HELPMENU);
    }

    // ClientListener methods implementation

    @Override
    public void hello() {
        synchronized (lock) {
            lock.notifyAll();
        }
    }

    @Override
    public void login() {
        synchronized (lock) {
            loginSuccessful = true;
            lock.notifyAll();
        }
    }

    @Override
    public void alreadyLoggedIn() {
        synchronized (lock) {
            lock.notifyAll();
        }
    }

    @Override
    public void move(int move) {
        System.out.println("Opponent played the move: " + move);
    }

    @Override
    public void list(String[] list) {
        StringBuilder stringBuilder = new StringBuilder();
        stringBuilder.append("All logged in clients: ");
        for (String client : list)  {
            stringBuilder.append(client).append(", ");
        }
        stringBuilder.delete(stringBuilder.length() - 2, stringBuilder.length() - 1);
        System.out.println(stringBuilder);
    }

    @Override
    public void newGame(String player1, String player2) {
        System.out.println("A new game has started! player1: " + player1 + " player2: " +player2);
    }

    @Override
    public void newGame() {

    }

    @Override
    public void gameOver(String reason, String winner) {
        if (winner == null) {
            System.out.println("The game has ended in a draw!");
        } else if (reason.equals("VICTORY")) {
            System.out.println("Player " + winner + " has won.");
        } else if (reason.equals("DISCONNECT")) {
            System.out.println("Player " + winner + " has won. The other player has disconnected");
        }
    }

    @Override
    public void connectionLost() {
        System.out.println("The connection was lost! Shutting down...");
        System.exit(0);
    }
}