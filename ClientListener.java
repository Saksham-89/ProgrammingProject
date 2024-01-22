package ProgrammingProject;

public interface ClientListener {
    void move(int move);
    void list(String[] list);
    void newGame();
    void gameOver(String reason, String winner);
}
