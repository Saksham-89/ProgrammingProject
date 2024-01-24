package ProgrammingProject;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class DotsAndBoxesGameTest {

    private DotsAndBoxesGame game;

    @BeforeEach
    public void setUp() {
        // Initialize the game before each test
        game = new DotsAndBoxesGame(); // Customize board size as needed
    }

    @Test
    public void testMoveIsPerformedCorrectly() {
        // Test whether a move is performed correctly
        game.makeMove(0, 0, 0, 1); // Player 1 places an edge
        assertEquals(1, game.getBoard().getPlayerAtEdge(0, 0, 0, 1)); // Check if the edge is owned by Player 1

        game.makeMove(0, 1, 0, 2); // Player 2 places an edge
        assertEquals(2, game.getBoard().getPlayerAtEdge(0, 1, 0, 2)); // Check if the edge is owned by Player 2

        // Add more test cases for different moves and scenarios
    }

    @Test
    public void testGameOverCondition() {
        // Test the game over condition
        assertFalse(game.isGameOver()); // Initially, the game should not be over

        // Simulate a complete game
        game.makeMove(0, 0, 0, 1);
        game.makeMove(0, 1, 0, 2);
        game.makeMove(0, 2, 1, 2);
        game.makeMove(1, 0, 1, 1);
        game.makeMove(1, 1, 1, 2);
        game.makeMove(1, 2, 2, 2);

        assertTrue(game.isGameOver()); // The game should be over after all boxes are claimed
    }

    @Test
    public void testFullGameFromStartToFinish() {
        // Test a full game from start to finish
        assertFalse(game.isGameOver()); // Initially, the game should not be over

        // Simulate a complete game with assertions between moves
        game.makeMove(0, 0, 0, 1);
        assertFalse(game.isGameOver()); // After 1st move, the game should not be over

        game.makeMove(0, 1, 0, 2);
        assertFalse(game.isGameOver()); // After 2nd move, the game should not be over

        game.makeMove(0, 2, 1, 2);
        assertFalse(game.isGameOver()); // After 3rd move, the game should not be over

        game.makeMove(1, 0, 1, 1);
        assertFalse(game.isGameOver()); // After 4th move, the game should not be over

        game.makeMove(1, 1, 1, 2);
        assertFalse(game.isGameOver()); // After 5th move, the game should not be over

        game.makeMove(1, 2, 2, 2);
        assertTrue(game.isGameOver()); // After 6th move, the game should be over
        assertEquals(2, game.getWinner()); // Player 2 should be the winner
    }
}
