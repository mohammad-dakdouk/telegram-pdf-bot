package com.dakdouk.pdftelegrambot;

import org.telegram.telegrambots.bots.TelegramLongPollingBot;
import org.telegram.telegrambots.meta.TelegramBotsApi;
import org.telegram.telegrambots.meta.api.methods.AnswerCallbackQuery;
import org.telegram.telegrambots.meta.api.methods.GetFile;
import org.telegram.telegrambots.meta.api.methods.send.SendDocument;
import org.telegram.telegrambots.meta.api.methods.send.SendMessage;
import org.telegram.telegrambots.meta.api.objects.CallbackQuery;
import org.telegram.telegrambots.meta.api.objects.Document;
import org.telegram.telegrambots.meta.api.objects.InputFile;
import org.telegram.telegrambots.meta.api.objects.Update;
import org.telegram.telegrambots.meta.api.objects.replykeyboard.InlineKeyboardMarkup;
import org.telegram.telegrambots.meta.api.objects.replykeyboard.buttons.InlineKeyboardButton;
import org.telegram.telegrambots.meta.exceptions.TelegramApiException;
import org.telegram.telegrambots.updatesreceivers.DefaultBotSession;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URI;
import java.net.URLConnection;
import java.nio.file.Files;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.util.logging.Level;
import java.util.logging.Logger;

// Apache PDFBox 3.x
import org.apache.pdfbox.Loader;
import org.apache.pdfbox.io.IOUtils;
import org.apache.pdfbox.multipdf.PDFMergerUtility;
import org.apache.pdfbox.pdmodel.PDDocument;

/**
 * Entry point. Its only job is to read the configuration, create the working
 * folder, and register the bot with Telegram.
 */
public class PdfTelegramBot {

    private static final Logger LOGGER = Logger.getLogger(PdfTelegramBot.class.getName());

    public static void main(String[] args) {
        // Set BOT_TOKEN in the process environment before starting the bot.
        String token = System.getenv("BOT_TOKEN");

        if (token == null || token.isBlank()) {
            LOGGER.severe("Missing BOT_TOKEN environment variable.");
            System.exit(1);
        }

        // Folder where downloaded / generated PDFs live temporarily.
        File downloadDir = new File("TelegramDownloads");
        if (!downloadDir.exists() && !downloadDir.mkdirs()) {
            LOGGER.severe("Could not create working directory: " + downloadDir.getAbsolutePath());
            System.exit(1);
        }

        try {
            TelegramBotsApi botsApi = new TelegramBotsApi(DefaultBotSession.class);
            MyPdfBot bot = new MyPdfBot(token);
            botsApi.registerBot(bot);

            // Runs when the JVM stops (Ctrl+C, service stop) so threads finish cleanly.
            Runtime.getRuntime().addShutdownHook(new Thread(bot::shutdown));

            LOGGER.info("Bot is running successfully!");
        } catch (TelegramApiException e) {
            LOGGER.log(Level.SEVERE, "Failed to start bot", e);
            System.exit(1);
        }
    }
}

/**
 * The bot itself. Uses long polling: our program repeatedly asks Telegram
 * "any new updates?" (no public URL or open port needed, which makes hosting easy).
 */
class MyPdfBot extends TelegramLongPollingBot {

    private static final Logger LOGGER = Logger.getLogger(MyPdfBot.class.getName());

    // ==================== LIMITS & STORAGE POLICY ====================

    private static final long MAX_FILE_SIZE_BYTES = 20L * 1024 * 1024; // 20 MB limit (Telegram bot download limit)

    // How often the maintenance task runs (expired sessions + forgotten files).
    private static final long CLEANUP_INTERVAL_MINUTES = 5;

    // A user who does nothing for this long loses their pending files (session reset).
    private static final long SESSION_IDLE_TIMEOUT_MILLIS = TimeUnit.MINUTES.toMillis(10);

    // Safety net: any file older than this is deleted even if no session owns it.
    // Must stay LARGER than SESSION_IDLE_TIMEOUT_MILLIS so sessions expire first.
    private static final long ORPHAN_FILE_MAX_AGE_MILLIS = TimeUnit.MINUTES.toMillis(20);

    // Refuse new uploads when the disk has less free space than this.
    private static final long MIN_FREE_SPACE_BYTES = 100L * 1024 * 1024; // 100 MB

    // ==================== ICONS ====================
    // Written as unicode escapes so the file stays pure ASCII and never breaks,
    // whatever encoding the editor / terminal / Maven uses.
    private static final String ICON_WAVE = "\uD83D\uDC4B";     // waving hand
    private static final String ICON_LIST = "\uD83D\uDCCB";     // clipboard
    private static final String ICON_MERGE = "\uD83D\uDD17";    // link
    private static final String ICON_SPLIT = "\u2702\uFE0F";    // scissors
    private static final String ICON_BOLT = "\u26A1";           // lightning
    private static final String ICON_DOWN = "\uD83D\uDC47";     // pointing down
    private static final String ICON_OK = "\u2705";             // green check
    private static final String ICON_WAIT = "\u23F3";           // hourglass
    private static final String ICON_INBOX = "\uD83D\uDCE5";    // inbox tray
    private static final String ICON_WARN = "\u26A0\uFE0F";     // warning
    private static final String ICON_ERROR = "\u274C";          // red cross
    private static final String ICON_TIP = "\uD83D\uDCA1";      // light bulb
    private static final String ICON_HELP = "\u2753";           // question mark
    private static final String ICON_PDF = "\uD83D\uDCC4";      // page
    private static final String BULLET = "\u2022";
    private static final String DASH = "\u2014";

    private final String botToken;
    private final File downloadDir = new File("TelegramDownloads");

    // A pool of 10 worker threads so one slow user (big download) doesn't block everyone else.
    private final ExecutorService workerPool = Executors.newFixedThreadPool(10);

    // Background task that deletes forgotten temp files. Daemon = it won't keep the JVM alive.
    private final ScheduledExecutorService cleanupScheduler = Executors.newSingleThreadScheduledExecutor(r -> {
        Thread t = new Thread(r);
        t.setDaemon(true);
        return t;
    });

    MyPdfBot(String botToken) {
        super(botToken);
        this.botToken = botToken;

        // On startup no session exists yet, so EVERY file left in the folder is garbage
        // from a previous run (crash, restart, ...). Delete all of them right now.
        cleanupOrphanedFiles(0);

        // Then keep cleaning every few minutes.
        cleanupScheduler.scheduleWithFixedDelay(this::runMaintenance,
                CLEANUP_INTERVAL_MINUTES, CLEANUP_INTERVAL_MINUTES, TimeUnit.MINUTES);
    }

    /** Graceful shutdown: stop accepting new work, then wait a bit for running work to finish. */
    public void shutdown() {
        LOGGER.info("Shutting down worker threads gracefully...");
        workerPool.shutdown();
        cleanupScheduler.shutdown();
        try {
            if (!workerPool.awaitTermination(10, TimeUnit.SECONDS)) {
                workerPool.shutdownNow(); // force-stop if still busy after 10 seconds
            }
        } catch (InterruptedException e) {
            workerPool.shutdownNow();
            Thread.currentThread().interrupt();
        }
        // The JVM is stopping: remove whatever temp files are still on disk.
        cleanupOrphanedFiles(0);
    }

    // ==================== SESSION STATE ====================

    private enum Mode {
        NONE, MERGE, SPLIT
    }

    /**
     * Everything we need to remember about ONE user (one chat) between messages.
     * The bot is a conversation: upload file -> send number -> send range -> ...
     * so we must store where each user is in that conversation.
     */
    private static class UserSession {

        Mode mode = Mode.NONE;
        File mergeFirstFile;        // first PDF waiting for the second one (merge)
        File splitPendingFile;      // PDF waiting to be split
        int totalPages = 0;         // page count of splitPendingFile (read once, reused)
        int targetPartsCount = 0;   // how many output files the user wants
        List<int[]> collectedRanges = new ArrayList<>(); // {start, end} for each output file
        final Deque<Runnable> pendingUpdates = new ArrayDeque<>();
        boolean processingUpdates;
        volatile long lastActivity = System.currentTimeMillis(); // last time this user sent anything
    }

    // chatId -> that user's session. ConcurrentHashMap because many threads access it.
    // Idle sessions are reset (their files deleted) by cleanupIdleSessions(); the empty
    // session objects stay in the map, they are tiny.
    private final Map<Long, UserSession> sessions = new ConcurrentHashMap<>();

    private UserSession sessionFor(long chatId) {
        return sessions.computeIfAbsent(chatId, id -> new UserSession());
    }

    // ==================== STATIC MESSAGES ====================

    private static final String WELCOME_MESSAGE
            = ICON_WAVE + " *Welcome to PDF Toolbox Bot!*\n\n"
            + "I am designed to help you *Merge* or *Split* your PDF files easily and securely.";

    private static final String CAPABILITIES_MESSAGE
            = ICON_LIST + " *Available Actions:*\n\n"
            + ICON_MERGE + " *Merge* " + DASH + " Combine two PDF files into a single document.\n"
            + ICON_SPLIT + " *Split* " + DASH + " Divide a PDF document into custom page ranges.\n\n"
            + ICON_BOLT + " *Quick Commands:*\n"
            + BULLET + " /merge " + DASH + " Start PDF merge process\n"
            + BULLET + " /split " + DASH + " Start PDF split process\n"
            + BULLET + " /cancel " + DASH + " Cancel active operation\n"
            + BULLET + " /help " + DASH + " Display capabilities menu\n\n"
            + ICON_DOWN + " Select an action below to get started:";

    @Override
    public String getBotToken() {
        return botToken;
    }

    @Override
    public String getBotUsername() {
        return "dakdouk_bot";
    }

    // ==================== UPDATE ENTRY POINT ====================

    /**
     * Called by the library for every update (message, button click, ...).
     * We hand the work to the thread pool so this method returns immediately.
     */
    @Override
    public void onUpdateReceived(Update update) {
        Long chatId = extractChatId(update);
        if (chatId == null) {
            if (update.hasCallbackQuery()) {
                answerCallback(update.getCallbackQuery().getId());
            }
            return;
        }

        UserSession session = sessionFor(chatId);
        session.lastActivity = System.currentTimeMillis();
        synchronized (session) {
            session.pendingUpdates.add(() -> processUpdate(chatId, session, update));
            if (session.processingUpdates) {
                return;
            }
            session.processingUpdates = true;
        }
        dispatchNextUpdate(session);
    }

    private void processUpdate(long chatId, UserSession session, Update update) {
        try {
            synchronized (session) {
                if (update.hasCallbackQuery()) {
                    handleCallback(chatId, session, update.getCallbackQuery());
                } else if (update.getMessage().hasDocument()) {
                    handleDocument(chatId, session, update.getMessage().getDocument());
                } else if (update.getMessage().hasText()) {
                    handleText(chatId, session, update.getMessage().getText().trim());
                }
            }
        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Error handling update", e);
            sendMsg(chatId, "An unexpected error occurred. Please try again or send /cancel.");
        }
    }

    private void dispatchNextUpdate(UserSession session) {
        Runnable nextUpdate;
        synchronized (session) {
            nextUpdate = session.pendingUpdates.poll();
            if (nextUpdate == null) {
                session.processingUpdates = false;
                return;
            }
        }

        try {
            workerPool.execute(() -> {
                try {
                    nextUpdate.run();
                } finally {
                    dispatchNextUpdate(session);
                }
            });
        } catch (java.util.concurrent.RejectedExecutionException e) {
            synchronized (session) {
                session.pendingUpdates.clear();
                session.processingUpdates = false;
            }
            LOGGER.log(Level.WARNING, "Update rejected because the bot is shutting down", e);
        }
    }

    /** Finds the chat id for the two update types we handle, or null for anything else. */
    private Long extractChatId(Update update) {
        if (update.hasCallbackQuery()) {
            return update.getCallbackQuery().getMessage() == null
                    ? null
                    : update.getCallbackQuery().getMessage().getChatId();
        }
        if (update.hasMessage()) {
            return update.getMessage().getChatId();
        }
        return null;
    }

    // ==================== EVENT HANDLERS ====================

    /** Handles clicks on the inline buttons (Merge / Split / Help). */
    private void handleCallback(long chatId, UserSession session, CallbackQuery callbackQuery) {
        String data = callbackQuery.getData();

        // Tell Telegram we received the click (removes the loading spinner on the button).
        answerCallback(callbackQuery.getId());

        switch (data) {
            case "action_merge" ->
                startMergeMode(chatId, session);
            case "action_split" ->
                startSplitMode(chatId, session);
            case "action_help" ->
                sendHelp(chatId);
            default ->
                LOGGER.warning("Unknown callback data: " + data);
        }
    }

    /** Handles text messages: commands first, otherwise treat as input for the split flow. */
    private void handleText(long chatId, UserSession session, String text) {
        if (text.isEmpty()) {
            return;
        }

        // In groups Telegram sends commands as "/start@dakdouk_bot".
        // We take the first word and cut off the "@botname" part so both forms work.
        String command = text.toLowerCase().split("\\s+")[0];
        int atIndex = command.indexOf('@');
        if (atIndex > 0) {
            command = command.substring(0, atIndex);
        }

        switch (command) {
            case "/start" -> {
                resetSession(session);
                sendMsg(chatId, WELCOME_MESSAGE);
                sendMsg(chatId, CAPABILITIES_MESSAGE, mainMenuKeyboard());
            }
            case "/help" ->
                sendHelp(chatId);
            case "/cancel" -> {
                boolean active = session.mode != Mode.NONE;
                resetSession(session);
                sendMsg(chatId, active
                        ? "Current process cancelled. Send /merge or /split to restart."
                        : "No active action to cancel.");
            }
            case "/merge" ->
                startMergeMode(chatId, session);
            case "/split" ->
                startSplitMode(chatId, session);
            default -> {
                // Not a command: if we are waiting for split input (number or range), use it.
                if (command.startsWith("/")) {
                    sendMsg(chatId, "Unknown command. Send /help to view commands.");
                } else if (session.splitPendingFile != null) {
                    processSplitInstruction(chatId, session, text);
                } else if (session.mode == Mode.SPLIT || session.mode == Mode.MERGE) {
                    sendMsg(chatId, "Please upload a PDF file first (or send /cancel).");
                } else {
                    sendMsg(chatId, "Unrecognized input. Send /help to view commands.");
                }
            }
        }
    }

    private void sendHelp(long chatId) {
        sendMsg(chatId, CAPABILITIES_MESSAGE, mainMenuKeyboard());
    }

    private void startMergeMode(long chatId, UserSession session) {
        resetSession(session); // clear any previous half-finished operation
        session.mode = Mode.MERGE;
        sendMsg(chatId, ICON_MERGE + " *Merge Mode Activated*\n\nPlease upload the *first* PDF file.");
    }

    private void startSplitMode(long chatId, UserSession session) {
        // Because updates of one user are now processed one at a time (see onUpdateReceived),
        // we no longer need the old "if already SPLIT, ignore" guard: restarting is safe.
        resetSession(session);
        session.mode = Mode.SPLIT;
        sendMsg(chatId, ICON_SPLIT + " *Split Mode Activated*\n\nPlease upload the PDF file you wish to split.");
    }

    // ==================== DOCUMENT & HEAVY OPERATIONS ====================

    /** Validates an uploaded file, downloads it, then routes it to merge or split. */
    private void handleDocument(long chatId, UserSession session, Document doc) {
        // 1) Basic validation before doing any expensive work.
        String fileName = doc.getFileName();
        if (fileName == null || !fileName.toLowerCase(java.util.Locale.ROOT).endsWith(".pdf")) {
            sendMsg(chatId, "Invalid format! Please upload a valid `.pdf` document.");
            return;
        }

        Number fileSize = doc.getFileSize();
        if (fileSize != null && fileSize.longValue() > MAX_FILE_SIZE_BYTES) {
            sendMsg(chatId, "File exceeds maximum size limit of 20MB.");
            return;
        }

        if (session.mode == Mode.NONE) {
            sendMsg(chatId, "Please choose an action first from the menu:", mainMenuKeyboard());
            return;
        }

        // 1b) Disk guard: do not start a download when the server is almost out of space.
        //     (getUsableSpace() returns 0 when it cannot tell, so 0 is treated as "unknown".)
        long freeSpace = downloadDir.getUsableSpace();
        if (freeSpace > 0 && freeSpace < MIN_FREE_SPACE_BYTES) {
            LOGGER.warning("Low disk space (" + (freeSpace / (1024 * 1024)) + " MB free), upload refused.");
            sendMsg(chatId, ICON_WARN + " The server is busy right now. Please try again in a few minutes.");
            return;
        }

        // 2) Download from Telegram servers to our disk.
        sendMsg(chatId, ICON_INBOX + " Downloading document, please wait...");
        File downloadedFile = downloadPdfFile(doc);
        if (downloadedFile == null) {
            sendMsg(chatId, "Failed to download the document. Please try sending it again.");
            return;
        }

        // 3) Make sure the file is a real, readable PDF. We read the page count ONCE here
        //    and pass it along instead of re-opening the file again and again.
        int pageCount = getPageCount(downloadedFile);
        if (pageCount <= 0) {
            downloadedFile.delete();
            sendMsg(chatId, "Corrupted or password-protected PDF. Please upload a valid file.");
            return;
        }

        // 4) Route by the user's current mode. If anything unexpected blows up, the file
        //    must not stay on disk, so we delete it and reset the session before rethrowing.
        try {
            switch (session.mode) {
                case MERGE ->
                    handleMergeDocument(chatId, session, downloadedFile);
                case SPLIT ->
                    handleSplitDocument(chatId, session, downloadedFile, pageCount);
                default ->
                    downloadedFile.delete();
            }
        } catch (RuntimeException e) {
            downloadedFile.delete();
            resetSession(session);
            throw e;
        }
    }

    /** Merge flow: store the first file, and when the second arrives, merge and send. */
    private void handleMergeDocument(long chatId, UserSession session, File downloadedFile) {
        File firstFile = session.mergeFirstFile;

        // No first file yet, or it was already removed by the cleanup task:
        // treat the new upload as the first one.
        if (firstFile == null || !firstFile.exists()) {
            boolean expired = firstFile != null;
            session.mergeFirstFile = downloadedFile;
            sendMsg(chatId, expired
                    ? ICON_WARN + " Your previous upload expired and was removed. This file is now the *first* PDF.\n\nPlease upload the *second* PDF file."
                    : ICON_OK + " First PDF received! Now upload the *second* PDF file.");
            return;
        }

        File mergedResult = null;
        try {
            sendMsg(chatId, ICON_WAIT + " Merging documents...");
            mergedResult = mergePdfFiles(firstFile, downloadedFile);

            if (mergedResult == null) {
                sendMsg(chatId, "An error occurred during merging. Please try again.");
                return;
            }
            if (sendDoc(chatId, mergedResult, "Merged.pdf")) {
                sendMsg(chatId, ICON_OK + " Merged successfully! The document has been sent.");
            } else {
                sendMsg(chatId, "The merged PDF could not be sent. Please re-upload both PDFs and retry.");
            }
        } finally {
            // Whatever happened above (success, failure, exception): nothing stays on disk.
            if (mergedResult != null) {
                mergedResult.delete();
            }
            firstFile.delete();
            downloadedFile.delete();
            resetSession(session);
        }
    }

    /** Split flow, step 0: store the file and ask how many output files the user wants. */
    private void handleSplitDocument(long chatId, UserSession session, File downloadedFile, int pageCount) {
        if (pageCount <= 1) {
            downloadedFile.delete();
            sendMsg(chatId, "This PDF has only 1 page and cannot be split.");
            resetSession(session);
            return;
        }

        // If the user uploaded a second file while one was pending, delete the old one
        // (otherwise it stays on disk) and restart the flow for the new file.
        if (session.splitPendingFile != null && session.splitPendingFile.exists()) {
            session.splitPendingFile.delete();
        }
        session.splitPendingFile = downloadedFile;
        session.totalPages = pageCount;
        session.targetPartsCount = 0;
        session.collectedRanges.clear();
        session.mode = Mode.SPLIT;

        sendMsg(chatId, ICON_PDF + " Document loaded successfully (" + pageCount + " pages total).\n\n"
                + "How many output PDF files do you want to create?\n"
                + ICON_TIP + " Send a number (Minimum: 2, Maximum: " + pageCount + ")");
    }

    /**
     * Split flow, steps 1 and 2:
     *  - Step 1: user sends HOW MANY output files they want.
     *  - Step 2: user sends a page range for each output file, one message per file.
     * When all ranges are collected we do the actual split.
     */
    private void processSplitInstruction(long chatId, UserSession session, String text) {
        File sourceFile = session.splitPendingFile;
        int pageCount = session.totalPages;

        // The cleanup task may have deleted the file if the user waited too long.
        if (sourceFile == null || !sourceFile.exists()) {
            sendMsg(chatId, "Document expired. Please re-upload your PDF file.");
            resetSession(session);
            return;
        }

        // The user is still active: refresh the file's timestamp so the orphan cleanup
        // does not delete it in the middle of the conversation.
        sourceFile.setLastModified(System.currentTimeMillis());

        // STEP 1: ask for number of split files
        if (session.targetPartsCount == 0) {
            try {
                int parts = Integer.parseInt(text);
                if (parts < 2 || parts > pageCount) {
                    sendMsg(chatId, ICON_WARN + " Invalid input! Please enter a number between 2 and " + pageCount + ".");
                    return;
                }
                session.targetPartsCount = parts;
                session.collectedRanges.clear();

                sendMsg(chatId, "Great! Enter page range for *File 1* (of " + parts + "):\n"
                        + ICON_TIP + " *Format Example:* `1-2` or `1` (Valid pages: 1 to " + pageCount + ")");
            } catch (NumberFormatException e) {
                sendMsg(chatId, ICON_WARN + " Please type a valid number for the total split files.");
            }
            return;
        }

        // STEP 2: collect ranges one by one, validating each before accepting it
        int currentPartIndex = session.collectedRanges.size() + 1;
        try {
            int[] range = parseSingleRange(text, pageCount);
            session.collectedRanges.add(range);

            if (session.collectedRanges.size() < session.targetPartsCount) {
                // Still need more ranges: ask for the next one.
                int nextPart = session.collectedRanges.size() + 1;
                sendMsg(chatId, ICON_OK + " Saved range for File " + (nextPart - 1) + " (Pages " + range[0] + " to " + range[1] + ").\n\n"
                        + "Now enter page range for *File " + nextPart + "* (of " + session.targetPartsCount + "):\n"
                        + ICON_TIP + " *Format Example:* `3-5` or `4` ");
            } else {
                // All ranges collected: do the split and send the results.
                sendMsg(chatId, ICON_WAIT + " Splitting PDF into " + session.targetPartsCount + " documents...");

                List<File> resultFiles = null;
                try {
                    resultFiles = splitPdfByRanges(sourceFile, session.collectedRanges);
                    if (resultFiles == null || resultFiles.isEmpty()) {
                        sendMsg(chatId, "Failed to split the PDF document. Please check page ranges.");
                    } else {
                        boolean allSent = true;
                        int partNo = 1;
                        for (File f : resultFiles) {
                            if (!sendDoc(chatId, f, "Part" + partNo + ".pdf")) {
                                allSent = false;
                                break;
                            }
                            partNo++;
                        }
                        sendMsg(chatId, allSent
                                ? ICON_OK + " All " + resultFiles.size() + " files generated and sent successfully!"
                                : "Not all split files could be sent. Please re-upload the source PDF and retry.");
                    }
                } finally {
                    if (resultFiles != null) {
                        for (File f : resultFiles) {
                            f.delete();
                        }
                    }
                    resetSession(session); // also deletes the source file
                }
            }
        } catch (IllegalArgumentException ex) {
            // parseSingleRange throws this with a user-friendly message; show it and ask again.
            sendMsg(chatId, ICON_ERROR + " " + ex.getMessage() + "\n\nPlease re-enter page range for *File " + currentPartIndex + "*:");
        }
    }

    // ==================== HELPER LOGIC ====================

    /**
     * Parses "3" or "3-5" into {start, end} and validates it against the page count.
     * Throws IllegalArgumentException with a readable message on bad input.
     */
    private int[] parseSingleRange(String text, int totalPages) {
        String part = text.trim();
        int start;
        int end;

        try {
            if (part.contains("-")) {
                String[] bounds = part.split("-");
                if (bounds.length != 2) {
                    throw new IllegalArgumentException("Invalid format! Use numbers separated by a dash e.g., 1-2");
                }
                start = Integer.parseInt(bounds[0].trim());
                end = Integer.parseInt(bounds[1].trim());
            } else {
                start = end = Integer.parseInt(part);
            }
        } catch (NumberFormatException e) {
            // Without this the user would see Java's raw message: For input string: "abc"
            throw new IllegalArgumentException("Invalid format! Use numbers only, e.g., 1-2 or 4");
        }

        if (start < 1 || end > totalPages || start > end) {
            throw new IllegalArgumentException("Range out of bounds! Document total pages: " + totalPages);
        }

        return new int[]{start, end};
    }

    /** Returns the number of pages, or -1 if the file is missing, corrupted or encrypted. */
    private int getPageCount(File file) {
        if (file == null || !file.exists()) {
            LOGGER.warning("PDF file is missing.");
            return -1;
        }
        // try-with-resources closes the PDDocument automatically (frees memory/file handle).
        // We catch Exception (not only IOException): a malformed PDF can also throw a
        // RuntimeException, and in that case the caller must still delete the file.
        try (PDDocument document = Loader.loadPDF(file)) {
            return document.getNumberOfPages();
        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Could not read PDF " + file.getAbsolutePath(), e);
            return -1;
        }
    }

    /** Downloads a file from Telegram servers into the TelegramDownloads folder. */
    private File downloadPdfFile(Document doc) {
        File localFile = null;
        try {
            // Step 1: ask Telegram where the file is stored (gives us a file path).
            GetFile getFileMethod = new GetFile();
            getFileMethod.setFileId(doc.getFileId());
            org.telegram.telegrambots.meta.api.objects.File telegramFile = execute(getFileMethod);
            if (telegramFile == null || telegramFile.getFilePath() == null) {
                throw new IOException("Telegram did not return a file path");
            }

            // Step 2: download it through the Bot API file URL.
            String fileUrl = "https://api.telegram.org/file/bot" + getBotToken() + "/" + telegramFile.getFilePath();
            localFile = Files.createTempFile(downloadDir.toPath(), "telegram-", ".pdf").toFile();

            URLConnection connection = URI.create(fileUrl).toURL().openConnection();
            connection.setConnectTimeout(15_000);
            connection.setReadTimeout(30_000);
            connection.setUseCaches(false);
            try (InputStream in = connection.getInputStream();
                    OutputStream out = Files.newOutputStream(localFile.toPath())) {
                byte[] buffer = new byte[8192];
                long totalBytes = 0;
                int bytesRead;
                while ((bytesRead = in.read(buffer)) != -1) {
                    totalBytes += bytesRead;
                    if (totalBytes > MAX_FILE_SIZE_BYTES) {
                        throw new IOException("Downloaded file exceeds the 20 MB limit");
                    }
                    out.write(buffer, 0, bytesRead);
                }
            }

            return localFile;
        } catch (Exception e) {
            if (localFile != null) {
                localFile.delete();
            }
            String message = e.getMessage();
            if (message != null) {
                message = message.replace(getBotToken(), "[REDACTED]");
            }
            LOGGER.log(Level.SEVERE, "Download error (" + e.getClass().getSimpleName() + "): " + message);
            return null;
        }
    }

    /** Merges file1 followed by file2 into a new file. Returns null on failure. */
    private File mergePdfFiles(File file1, File file2) {
        File mergedFile = null;
        try {
            mergedFile = Files.createTempFile(downloadDir.toPath(), "Merged_", ".pdf").toFile();
            PDFMergerUtility merger = new PDFMergerUtility();
            merger.setDestinationFileName(mergedFile.getAbsolutePath());
            merger.addSource(file1);
            merger.addSource(file2);
            // PDFBox 3 needs to know how to buffer data while merging.
            // Memory-only is fine here because files are limited to 20 MB.
            merger.mergeDocuments(IOUtils.createMemoryOnlyStreamCache());
            return mergedFile;
        } catch (IOException e) {
            LOGGER.log(Level.SEVERE, "Merge failed", e);
            if (mergedFile != null) {
                mergedFile.delete();
            }
            return null;
        }
    }

    /**
     * Creates one new PDF per range. Ranges are 1-based and inclusive, e.g. {2,4} = pages 2,3,4.
     * Returns null (and deletes partial results) if anything fails.
     */
    private List<File> splitPdfByRanges(File sourceFile, List<int[]> ranges) {
        List<File> outputFiles = new ArrayList<>();

        try (PDDocument sourceDoc = Loader.loadPDF(sourceFile)) {
            int partNumber = 1;
            for (int[] range : ranges) {
                File outFile = Files.createTempFile(downloadDir.toPath(), "Split_Part" + partNumber + "_", ".pdf").toFile();
                outputFiles.add(outFile);
                try (PDDocument newDoc = new PDDocument()) {
                    for (int i = range[0]; i <= range[1]; i++) {
                        // PDFBox pages are 0-based, our ranges are 1-based, hence i - 1.
                        newDoc.importPage(sourceDoc.getPage(i - 1));
                    }
                    newDoc.save(outFile);
                }
                partNumber++;
            }
            return outputFiles;
        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Split failed", e);
            for (File f : outputFiles) {
                if (f.exists()) {
                    f.delete();
                }
            }
            return null;
        }
    }

    // ==================== MAINTENANCE (keeps the disk from filling up) ====================

    /**
     * Runs every CLEANUP_INTERVAL_MINUTES. Order matters: first expire idle sessions
     * (which deletes their files), then sweep any leftover old files.
     * The try/catch is essential: if a scheduled task ever throws, Java silently
     * cancels ALL its future runs and the cleanup would stop forever.
     */
    private void runMaintenance() {
        try {
            cleanupIdleSessions();
            cleanupOrphanedFiles(ORPHAN_FILE_MAX_AGE_MILLIS);
        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Maintenance task failed", e);
        }
    }

    /**
     * Resets every session whose user has been silent for too long, which deletes the
     * PDF they left waiting (first merge file / pending split file).
     */
    private void cleanupIdleSessions() {
        long now = System.currentTimeMillis();
        for (Map.Entry<Long, UserSession> entry : sessions.entrySet()) {
            long chatId = entry.getKey();
            UserSession session = entry.getValue();

            if (now - session.lastActivity < SESSION_IDLE_TIMEOUT_MILLIS) {
                continue;
            }

            boolean hadActiveFlow;
            synchronized (session) {
                // Re-check under the lock: the user may have just sent something.
                if (session.processingUpdates
                        || !session.pendingUpdates.isEmpty()
                        || System.currentTimeMillis() - session.lastActivity < SESSION_IDLE_TIMEOUT_MILLIS) {
                    continue;
                }
                hadActiveFlow = session.mode != Mode.NONE;
                resetSession(session);
            }

            // Tell the user only if they actually had something in progress (outside the lock).
            if (hadActiveFlow) {
                sendMsg(chatId, ICON_WAIT + " Session expired due to inactivity and your temporary files were deleted.\n\n"
                        + "Send /merge or /split to start again.");
            }
        }
    }

    /**
     * Deletes every file in the working folder that is at least maxAgeMillis old.
     * maxAgeMillis = 0 deletes everything (used at startup and shutdown).
     */
    private void cleanupOrphanedFiles(long maxAgeMillis) {
        File[] files = downloadDir.listFiles();
        if (files == null) {
            return;
        }
        long now = System.currentTimeMillis();
        for (File f : files) {
            if (f.isFile() && now - f.lastModified() >= maxAgeMillis) {
                if (!f.delete()) {
                    LOGGER.warning("Could not delete temp file: " + f.getName());
                }
            }
        }
    }

    // ==================== UI & TELEGRAM METHOD WRAPPERS ====================

    /** Builds the inline keyboard: [Merge][Split] on the first row, [Help] on the second. */
    private InlineKeyboardMarkup mainMenuKeyboard() {
        InlineKeyboardButton mergeBtn = InlineKeyboardButton.builder().text(ICON_MERGE + " Merge PDFs").callbackData("action_merge").build();
        InlineKeyboardButton splitBtn = InlineKeyboardButton.builder().text(ICON_SPLIT + " Split PDF").callbackData("action_split").build();
        InlineKeyboardButton helpBtn = InlineKeyboardButton.builder().text(ICON_HELP + " Help").callbackData("action_help").build();

        return InlineKeyboardMarkup.builder()
                .keyboardRow(List.of(mergeBtn, splitBtn))
                .keyboardRow(Collections.singletonList(helpBtn))
                .build();
    }

    /**
     * Clears a user's state and deletes any temp files they had pending.
     * (chatId parameter removed: it was never used.)
     */
    private void resetSession(UserSession session) {
        if (session.mergeFirstFile != null && session.mergeFirstFile.exists()) {
            session.mergeFirstFile.delete();
        }
        if (session.splitPendingFile != null && session.splitPendingFile.exists()) {
            session.splitPendingFile.delete();
        }

        session.mode = Mode.NONE;
        session.mergeFirstFile = null;
        session.splitPendingFile = null;
        session.totalPages = 0;
        session.targetPartsCount = 0;
        session.collectedRanges.clear();
    }

    private void answerCallback(String callbackQueryId) {
        try {
            execute(AnswerCallbackQuery.builder().callbackQueryId(callbackQueryId).build());
        } catch (TelegramApiException e) {
            LOGGER.log(Level.WARNING, "Failed to acknowledge callback", e);
        }
    }

    /** Sends a message without a keyboard. */
    private void sendMsg(long chatId, String text) {
        sendMsg(chatId, text, null);
    }

    /**
     * Single method for ALL text messages (replaces the old sendMsg + sendMarkdown pair).
     * FIX: every message now uses Markdown, so *bold* and `code` render correctly everywhere.
     * If Telegram rejects the Markdown (e.g. a stray "_" or "*"), we retry as plain text
     * so the user still gets the message instead of nothing.
     */
    private void sendMsg(long chatId, String text, InlineKeyboardMarkup keyboard) {
        SendMessage message = SendMessage.builder()
                .chatId(String.valueOf(chatId))
                .text(text)
                .parseMode("Markdown")
                .replyMarkup(keyboard)
                .build();

        try {
            execute(message);
        } catch (TelegramApiException e) {
            LOGGER.log(Level.WARNING, "Markdown send failed, retrying as plain text", e);
            message.setParseMode(null);
            try {
                execute(message);
            } catch (TelegramApiException e2) {
                LOGGER.log(Level.WARNING, "Failed to send message", e2);
            }
        }
    }

    private boolean sendDoc(long chatId, File file, String displayName) {
        try {
            execute(SendDocument.builder().chatId(String.valueOf(chatId)).document(new InputFile(file, displayName)).build());
            return true;
        } catch (TelegramApiException e) {
            LOGGER.log(Level.WARNING, "Failed to send document", e);
            return false;
        }
    }
}