package group.chapmanlaw.texasrulesandstandards;

import com.jcraft.jsch.ChannelSftp;
import com.jcraft.jsch.JSch;
import com.jcraft.jsch.JSchException;
import com.jcraft.jsch.Session;
import com.jcraft.jsch.SftpException;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.nio.file.StandardOpenOption;
import java.time.Duration;
import java.time.Instant;
import java.time.LocalDate;
import java.time.ZoneId;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeParseException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HexFormat;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.Base64;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.logging.ConsoleHandler;
import java.util.logging.FileHandler;
import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;
import org.apache.pdfbox.pdmodel.PDDocument;
import org.apache.pdfbox.pdmodel.PDPage;
import org.apache.pdfbox.pdmodel.PDPageContentStream;
import org.apache.pdfbox.pdmodel.common.PDRectangle;
import org.apache.pdfbox.pdmodel.font.PDFont;
import org.apache.pdfbox.pdmodel.font.PDType1Font;
import org.apache.pdfbox.pdmodel.interactive.action.PDActionGoTo;
import org.apache.pdfbox.pdmodel.interactive.annotation.PDAnnotationLink;
import org.apache.pdfbox.pdmodel.interactive.documentnavigation.destination.PDPageFitWidthDestination;
import org.apache.tika.exception.TikaException;
import org.apache.tika.metadata.Metadata;
import org.apache.tika.parser.ParseContext;
import org.apache.tika.parser.pdf.PDFParser;
import org.apache.tika.sax.BodyContentHandler;
import org.jsoup.Jsoup;
import org.jsoup.nodes.Document;
import org.jsoup.nodes.Element;
import org.jsoup.nodes.Node;
import org.jsoup.nodes.TextNode;
import org.xml.sax.SAXException;

public class app {

    private static final URI SOURCE_PAGE_URI = URI.create("https://www.txcourts.gov/rules-forms/rules-standards/");
    private static final Path DATA_DIRECTORY = Path.of("data");
    private static final Path METADATA_FILE = Path.of("rules-standards-metadata.properties");
    private static final Path LEGACY_METADATA_FILE = DATA_DIRECTORY.resolve("rules-standards-metadata.properties");
    private static final String LOG_FILE_PATTERN = Path.of("rules-standards-%g.log").toString();
    private static final int LOG_FILE_LIMIT_BYTES = 1_048_576;
    private static final int LOG_FILE_ROTATION_COUNT = 5;
    private static final String RULES_SECTION_HEADING = "Statewide Rules";
    private static final String STANDARDS_SECTION_HEADING = "Statewide Standards";
    private static final String STORAGE_ENGINE_LOCAL = "local";
    private static final String STORAGE_ENGINE_SFTP = "sftp";
    private static final String STORAGE_ENGINE_WEBDAV = "webdav";
    private static final String COMBINED_PDF_ENABLED_PROPERTY = "combined.pdf.enabled";
    private static final String COMBINED_PDF_ENABLED_ENV = "COMBINED_PDF_ENABLED";
    private static final boolean DEFAULT_COMBINED_PDF_ENABLED = false;
    private static final String TEXT_EXTRACTION_ENABLED_PROPERTY = "text.extraction.enabled";
    private static final String TEXT_EXTRACTION_ENABLED_ENV = "TEXT_EXTRACTION_ENABLED";
    private static final boolean DEFAULT_TEXT_EXTRACTION_ENABLED = false;
    private static final String TEXT_OUTPUT_DIRECTORY = "txt";
    private static final String COMBINED_NEW_FILE_NAME = "combined_new.pdf";
    private static final String COMBINED_PREVIOUS_FILE_NAME = "combined_previous.pdf";
    private static final Set<String> DOCUMENT_EXTENSIONS = Set.of("pdf", "doc", "docx");
    private static final String HTTP_USER_AGENT = "texas-rules-and-standards-sync/1.0 (+https://www.txcourts.gov/)";
    private static final Pattern DATE_PATTERN = Pattern.compile(
            "(?i)(January|February|March|April|May|June|July|August|September|October|November|December)\\s+\\d{1,2},\\s+\\d{4}");
    private static final Pattern HTML_ANCHOR_PATTERN = Pattern.compile(
            "<a\\b[^>]*href\\s*=\\s*['\"]([^'\"]+)['\"][^>]*>(.*?)</a>",
            Pattern.CASE_INSENSITIVE | Pattern.DOTALL);
    private static final DateTimeFormatter LAST_AMENDED_FORMAT = DateTimeFormatter.ofPattern("MMMM d, uuuu", Locale.US);
    private static final float TOC_PAGE_MARGIN = 50f;
    private static final float TOC_LINE_HEIGHT = 16f;
    private static final float TOC_TITLE_FONT_SIZE = 20f;
    private static final float TOC_ENTRY_FONT_SIZE = 12f;
    private static final Logger LOGGER = Logger.getLogger(app.class.getName());

    public static void main(String[] args) {
        try {
            Files.createDirectories(DATA_DIRECTORY);
            configureLogging();

            LOGGER.info("Starting Texas rules and standards sync.");
            LOGGER.info("Source page: " + SOURCE_PAGE_URI);
            LOGGER.info("Data directory: " + DATA_DIRECTORY.toAbsolutePath());

            StorageSettings storageSettings = resolveStorageSettings();
            boolean combinedPdfEnabled = resolveCombinedPdfEnabled();
            boolean textExtractionEnabled = resolveTextExtractionEnabled();
            LOGGER.info("Configured storage engine: " + storageSettings.engine());
            LOGGER.info("Configured combined PDF generation: " + (combinedPdfEnabled ? "enabled" : "disabled"));
            LOGGER.info("Configured text extraction: " + (textExtractionEnabled ? "enabled" : "disabled"));
            if (STORAGE_ENGINE_SFTP.equals(storageSettings.engine())) {
                LOGGER.info("Configured SFTP endpoint: " + storageSettings.sftpEndpoint());
            } else if (STORAGE_ENGINE_WEBDAV.equals(storageSettings.engine())) {
                LOGGER.info("Configured WebDAV endpoint: " + storageSettings.webDavEndpoint());
            }

            Properties previousMetadata = loadMetadata();
            LOGGER.info("Loaded metadata entries: " + countDocumentIds(previousMetadata));

            HttpClient httpClient = HttpClient.newBuilder()
                    .followRedirects(HttpClient.Redirect.NORMAL)
                    .connectTimeout(Duration.ofSeconds(30))
                    .build();

            String html = fetchHtml(httpClient, SOURCE_PAGE_URI);
            List<DocumentRecord> extractedDocuments = extractDocumentRecords(html, SOURCE_PAGE_URI);
            List<DocumentRecord> documents = deduplicateDocuments(extractedDocuments);

            if (documents.isEmpty()) {
                LOGGER.severe("No statewide rules/standards documents were found on the source page. The page format may have changed.");
                System.exit(2);
            }

            LOGGER.info("Discovered " + documents.size() + " candidate document(s) to track.");

            try (StorageEngine storageEngine = createStorageEngine(storageSettings)) {
                LOGGER.info("Active storage engine: " + storageEngine.name());
                LOGGER.info("Storage root: " + storageEngine.describeRoot());

                Properties updatedMetadata = new Properties();
                SyncStats stats = syncDocuments(httpClient, documents, previousMetadata, updatedMetadata, storageEngine);
                if (combinedPdfEnabled) {
                    CombinedBuildResult combinedBuild = buildCombinedPdfs(
                            documents,
                            storageEngine,
                            stats.downloaded() > 0,
                            stats.updatedDocumentIds()
                    );
                    applyCombinedMetadata(updatedMetadata, combinedBuild, previousMetadata);
                } else {
                    LOGGER.info("Skipping combined PDF generation; combined PDF output is disabled.");
                    applyCombinedMetadata(updatedMetadata, CombinedBuildResult.none(), previousMetadata);
                }
                if (textExtractionEnabled) {
                    extractPdfTextArtifacts(documents, storageEngine, updatedMetadata, previousMetadata);
                } else {
                    LOGGER.info("Skipping .txt extraction artifacts; text extraction is disabled.");
                    preserveTextArtifactMetadata(updatedMetadata, previousMetadata);
                }
                updatedMetadata.setProperty(COMBINED_PDF_ENABLED_PROPERTY, Boolean.toString(combinedPdfEnabled));
                updatedMetadata.setProperty(TEXT_EXTRACTION_ENABLED_PROPERTY, Boolean.toString(textExtractionEnabled));
                updatedMetadata.setProperty("storage.engine", storageEngine.name());
                updatedMetadata.setProperty("storage.root", storageEngine.describeRoot());
                writeMetadata(updatedMetadata);

                LOGGER.info("Sync completed.");
                LOGGER.info("Summary: downloaded=" + stats.downloaded()
                        + ", updated=" + stats.updated()
                        + ", skipped=" + stats.skipped()
                        + ", failed=" + stats.failed());
                LOGGER.info("Metadata written to " + METADATA_FILE.toAbsolutePath());
            }
        } catch (Exception ex) {
            LOGGER.log(Level.SEVERE, "Sync failed.", ex);
            System.exit(1);
        }
    }

    private static StorageSettings resolveStorageSettings() {
        String configuredEngine = normalizeStorageEngine(readConfig("storage.engine", "STORAGE_ENGINE", STORAGE_ENGINE_LOCAL));
        if (STORAGE_ENGINE_LOCAL.equals(configuredEngine)) {
            return StorageSettings.local();
        }
        if (STORAGE_ENGINE_SFTP.equals(configuredEngine)) {
            String host = readRequiredConfig("storage.sftp.host", "SFTP_HOST");
            int port = parsePositiveInt(readConfig("storage.sftp.port", "SFTP_PORT", "22"), "storage.sftp.port/SFTP_PORT");
            String username = readRequiredConfig("storage.sftp.username", "SFTP_USERNAME");
            String password = readRequiredConfig("storage.sftp.password", "SFTP_PASSWORD");
            String remoteDirectory = normalizeRemoteDirectory(
                    readConfig("storage.sftp.remoteDir", "SFTP_REMOTE_DIR", "/texas-rules-and-standards"));
            int timeoutSeconds = parsePositiveInt(
                    readConfig("storage.sftp.timeoutSeconds", "SFTP_TIMEOUT_SECONDS", "30"),
                    "storage.sftp.timeoutSeconds/SFTP_TIMEOUT_SECONDS");
            return StorageSettings.sftp(host, port, username, password, remoteDirectory, timeoutSeconds);
        }
        if (STORAGE_ENGINE_WEBDAV.equals(configuredEngine)) {
            String baseUrl = normalizeWebDavBaseUrl(readRequiredConfig("storage.webdav.baseUrl", "WEBDAV_BASE_URL"));
            String username = readRequiredConfig("storage.webdav.username", "WEBDAV_USERNAME");
            String password = readRequiredConfig("storage.webdav.password", "WEBDAV_PASSWORD");
            String remoteDirectory = normalizeRemoteDirectory(
                    readConfig("storage.webdav.remoteDir", "WEBDAV_REMOTE_DIR", "/texas-rules-and-standards"));
            int timeoutSeconds = parsePositiveInt(
                    readConfig("storage.webdav.timeoutSeconds", "WEBDAV_TIMEOUT_SECONDS", "30"),
                    "storage.webdav.timeoutSeconds/WEBDAV_TIMEOUT_SECONDS");
            return StorageSettings.webDav(baseUrl, username, password, remoteDirectory, timeoutSeconds);
        }
        throw new IllegalArgumentException(
                "Unsupported storage engine '" + configuredEngine + "'. Supported values: local, sftp, webdav.");
    }

    private static boolean resolveCombinedPdfEnabled() {
        String raw = readConfig(
                COMBINED_PDF_ENABLED_PROPERTY,
                COMBINED_PDF_ENABLED_ENV,
                Boolean.toString(DEFAULT_COMBINED_PDF_ENABLED)
        );
        return parseBooleanConfig(raw, COMBINED_PDF_ENABLED_PROPERTY + "/" + COMBINED_PDF_ENABLED_ENV);
    }

    private static boolean resolveTextExtractionEnabled() {
        String raw = readConfig(
                TEXT_EXTRACTION_ENABLED_PROPERTY,
                TEXT_EXTRACTION_ENABLED_ENV,
                Boolean.toString(DEFAULT_TEXT_EXTRACTION_ENABLED)
        );
        return parseBooleanConfig(raw, TEXT_EXTRACTION_ENABLED_PROPERTY + "/" + TEXT_EXTRACTION_ENABLED_ENV);
    }

    private static StorageEngine createStorageEngine(StorageSettings settings) throws IOException {
        if (STORAGE_ENGINE_SFTP.equals(settings.engine())) {
            return new SftpStorageEngine(settings);
        }
        if (STORAGE_ENGINE_WEBDAV.equals(settings.engine())) {
            return new WebDavStorageEngine(settings);
        }
        return new LocalStorageEngine(DATA_DIRECTORY);
    }

    private static void configureLogging() throws IOException {
        LOGGER.setUseParentHandlers(false);
        LOGGER.setLevel(Level.INFO);

        for (Handler handler : LOGGER.getHandlers()) {
            LOGGER.removeHandler(handler);
            handler.close();
        }

        Formatter formatter = new SimpleLogFormatter();

        ConsoleHandler consoleHandler = new ConsoleHandler();
        consoleHandler.setLevel(Level.INFO);
        consoleHandler.setFormatter(formatter);
        LOGGER.addHandler(consoleHandler);

        FileHandler fileHandler = new FileHandler(LOG_FILE_PATTERN, LOG_FILE_LIMIT_BYTES, LOG_FILE_ROTATION_COUNT, true);
        fileHandler.setLevel(Level.ALL);
        fileHandler.setFormatter(formatter);
        LOGGER.addHandler(fileHandler);
    }

    private static Properties loadMetadata() throws IOException {
        Properties metadata = new Properties();
        Path metadataSource = METADATA_FILE;
        if (!Files.exists(metadataSource)) {
            if (Files.exists(LEGACY_METADATA_FILE)) {
                metadataSource = LEGACY_METADATA_FILE;
                LOGGER.info("Using legacy metadata path: " + LEGACY_METADATA_FILE.toAbsolutePath());
            } else {
                return metadata;
            }
        }

        if (!Files.exists(metadataSource)) {
            return metadata;
        }

        String raw = Files.readString(metadataSource, StandardCharsets.UTF_8);
        try (StringReader reader = new StringReader(raw)) {
            metadata.load(reader);
        }
        return metadata;
    }

    private static void writeMetadata(Properties metadata) throws IOException {
        StringWriter writer = new StringWriter();
        metadata.store(writer, "Texas rules and standards metadata");
        Files.writeString(
                METADATA_FILE,
                writer.toString(),
                StandardCharsets.UTF_8,
                StandardOpenOption.CREATE,
                StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE
        );
    }

    private static String fetchHtml(HttpClient httpClient, URI sourceUri) throws IOException, InterruptedException {
        LOGGER.info("Fetching source page HTML.");
        HttpRequest request = HttpRequest.newBuilder(sourceUri)
                .GET()
                .timeout(Duration.ofSeconds(45))
                .header("User-Agent", HTTP_USER_AGENT)
                .header("Accept", "text/html,application/xhtml+xml")
                .build();

        HttpResponse<String> response = httpClient.send(request, HttpResponse.BodyHandlers.ofString(StandardCharsets.UTF_8));
        int statusCode = response.statusCode();
        if (statusCode < 200 || statusCode >= 300) {
            throw new IOException("Failed to fetch source page. HTTP status " + statusCode);
        }

        LOGGER.info("Fetched source page HTML successfully (HTTP " + statusCode + ").");
        return response.body();
    }

    private static List<DocumentRecord> extractDocumentRecords(String html, URI sourcePage) {
        LOGGER.info("Extracting links and last amended dates from the page.");
        Document document = Jsoup.parse(html, sourcePage.toString());
        List<DocumentRecord> records = new ArrayList<>();

        records.addAll(extractSectionRecords(document, RULES_SECTION_HEADING, "rules"));
        records.addAll(extractSectionRecords(document, STANDARDS_SECTION_HEADING, "standards"));

        if (records.isEmpty()) {
            LOGGER.warning("Structured extraction returned no records. Trying HTML fallback extraction for CSS/JS markup changes.");
            records.addAll(extractFallbackRecordsFromRawHtml(html, sourcePage));
        }

        return records;
    }

    private static List<DocumentRecord> extractSectionRecords(Document document, String sectionHeading, String sectionKey) {
        Element heading = findHeadingByText(document, sectionHeading);
        if (heading == null) {
            LOGGER.warning("Could not find section heading: " + sectionHeading);
            return Collections.emptyList();
        }

        List<Element> sectionSiblings = collectSectionSiblings(heading);
        if (sectionSiblings.isEmpty()) {
            LOGGER.warning("No sibling content found after heading: " + sectionHeading);
            return Collections.emptyList();
        }

        List<SectionToken> tokens = new ArrayList<>();
        for (Element sibling : sectionSiblings) {
            collectSectionTokens(sibling, tokens);
        }

        List<DocumentRecord> records = new ArrayList<>();
        for (int i = 0; i < tokens.size(); i++) {
            SectionToken token = tokens.get(i);
            if (token.type() != TokenType.ANCHOR) {
                continue;
            }
            if (!looksLikeDocumentUrl(token.href())) {
                continue;
            }

            String title = normalizeWhitespace(token.text());
            if (title.isBlank()) {
                continue;
            }

            String lastAmended = findDateNearby(tokens, i);
            LocalDate lastAmendedDate = parseLastAmended(lastAmended);
            URI documentUri = resolveUri(SOURCE_PAGE_URI, token.href());
            if (documentUri == null) {
                LOGGER.warning("Skipping anchor with invalid URI: " + token.href());
                continue;
            }

            records.add(buildDocumentRecord(title, documentUri, sectionKey, lastAmended, lastAmendedDate));
        }

        LOGGER.info("Section '" + sectionHeading + "' yielded " + records.size() + " candidate document(s).");
        return records;
    }

    private static List<DocumentRecord> extractFallbackRecordsFromRawHtml(String html, URI sourcePage) {
        List<DocumentRecord> records = new ArrayList<>();
        String loweredHtml = html.toLowerCase(Locale.US);

        Matcher matcher = HTML_ANCHOR_PATTERN.matcher(html);
        while (matcher.find()) {
            String href = matcher.group(1);
            if (!looksLikeDocumentUrl(href)) {
                continue;
            }

            int contextStart = Math.max(0, matcher.start() - 2_500);
            String previousContext = loweredHtml.substring(contextStart, matcher.start());
            String sectionKey = inferSectionFromHtmlContext(previousContext);
            if (sectionKey == null) {
                continue;
            }

            String title = normalizeWhitespace(Jsoup.parse(matcher.group(2)).text());
            if (title.isBlank()) {
                continue;
            }

            int dateWindowEnd = Math.min(html.length(), matcher.end() + 450);
            String dateWindow = html.substring(matcher.start(), dateWindowEnd);
            String lastAmended = extractDateText(dateWindow);
            LocalDate lastAmendedDate = parseLastAmended(lastAmended);
            URI documentUri = resolveUri(sourcePage, href);
            if (documentUri == null) {
                continue;
            }

            records.add(buildDocumentRecord(title, documentUri, sectionKey, lastAmended, lastAmendedDate));
        }

        LOGGER.info("Fallback extraction yielded " + records.size() + " candidate document(s).");
        return records;
    }

    private static SyncStats syncDocuments(
            HttpClient httpClient,
            List<DocumentRecord> documents,
            Properties previousMetadata,
            Properties updatedMetadata,
            StorageEngine storageEngine
    ) throws IOException, InterruptedException {
        int downloaded = 0;
        int updated = 0;
        int skipped = 0;
        int failed = 0;
        Set<String> updatedDocumentIds = new LinkedHashSet<>();

        Set<String> ids = new LinkedHashSet<>();
        for (DocumentRecord document : documents) {
            ids.add(document.id());
            LOGGER.info("Evaluating: " + document.title());
            LOGGER.info("  URL: " + document.downloadUri());
            LOGGER.info("  Last amended: " + (document.lastAmendedRaw() == null ? "Unknown" : document.lastAmendedRaw()));
            LOGGER.info("  Storage target: " + storageEngine.describeTarget(document));

            String metadataPrefix = "doc." + document.id() + ".";
            String previousLastAmended = previousMetadata.getProperty(metadataPrefix + "lastAmended");
            String previousUrl = previousMetadata.getProperty(metadataPrefix + "url");
            String previousMd5New = firstNonBlank(
                    previousMetadata.getProperty(metadataPrefix + "md5.new"),
                    previousMetadata.getProperty(metadataPrefix + "md5"));
            String previousMd5Previous = previousMetadata.getProperty(metadataPrefix + "md5.previous");

            boolean storedCopyExists = storageEngine.exists(document);
            if ((previousMd5New == null || previousMd5New.isBlank()) && storedCopyExists) {
                previousMd5New = md5Hex(storageEngine.read(document.fileName()));
            }
            if ((previousMd5Previous == null || previousMd5Previous.isBlank())
                    && document.previousFileName() != null
                    && storageEngine.exists(document.previousFileName())) {
                previousMd5Previous = md5Hex(storageEngine.read(document.previousFileName()));
            }
            boolean shouldDownload;
            String reason;
            boolean previousHasAmendmentDate = previousLastAmended != null && !previousLastAmended.isBlank();
            boolean currentHasAmendmentDate = document.lastAmendedRaw() != null && !document.lastAmendedRaw().isBlank();

            if (!storedCopyExists) {
                shouldDownload = true;
                reason = "missing stored file";
            } else if (!previousHasAmendmentDate && !currentHasAmendmentDate) {
                String currentUrl = document.downloadUri().toString();
                boolean sameUrl = previousUrl != null
                        && !previousUrl.isBlank()
                        && previousUrl.equalsIgnoreCase(currentUrl);
                shouldDownload = !sameUrl;
                reason = sameUrl
                        ? "no amendment date and URL unchanged"
                        : "no amendment date and URL changed";
            } else if (!previousHasAmendmentDate) {
                shouldDownload = true;
                reason = "source now provides an amendment date";
            } else if (isAmended(previousLastAmended, document.lastAmendedRaw(), document.lastAmended())) {
                shouldDownload = true;
                reason = "amendment date changed (stored: '" + previousLastAmended + "', current: '"
                        + safeValue(document.lastAmendedRaw()) + "')";
            } else {
                shouldDownload = false;
                reason = "no amendment change detected";
            }

            if (shouldDownload) {
                LOGGER.info("  Action: download+store (" + reason + ")");
                try {
                    boolean isUpdate = storedCopyExists;
                    byte[] bytes = downloadDocument(httpClient, document.downloadUri());
                    String md5PreviousVersion = previousMd5Previous;
                    if (isUpdate) {
                        storageEngine.preservePrevious(document);
                        if (document.previousFileName() != null && storageEngine.exists(document.previousFileName())) {
                            md5PreviousVersion = md5Hex(storageEngine.read(document.previousFileName()));
                        }
                    }
                    storageEngine.write(document, bytes);
                    String md5NewVersion = md5Hex(bytes);
                    downloaded++;
                    if (isUpdate) {
                        updated++;
                        updatedDocumentIds.add(document.id());
                    }
                    LOGGER.info("  Result: download+store succeeded (" + bytes.length + " bytes)");
                    updateMetadataEntry(
                            updatedMetadata,
                            metadataPrefix,
                            document,
                            storageEngine,
                            md5NewVersion,
                            md5PreviousVersion
                    );
                } catch (IOException | InterruptedException ex) {
                    failed++;
                    LOGGER.log(Level.SEVERE, "  Result: download+store failed for '" + document.title() + "'", ex);
                    preservePreviousMetadata(updatedMetadata, previousMetadata, metadataPrefix, document, storageEngine);
                    if (ex instanceof InterruptedException) {
                        Thread.currentThread().interrupt();
                        throw ex;
                    }
                }
            } else {
                skipped++;
                LOGGER.info("  Action: skip (" + reason + ")");
                updateMetadataEntry(
                        updatedMetadata,
                        metadataPrefix,
                        document,
                        storageEngine,
                        previousMd5New,
                        previousMd5Previous
                );
            }
        }

        updatedMetadata.setProperty("tracked.ids", String.join(",", ids));
        updatedMetadata.setProperty("tracked.count", Integer.toString(ids.size()));
        updatedMetadata.setProperty("source.page", SOURCE_PAGE_URI.toString());
        updatedMetadata.setProperty("source.lastCheckedAt", Instant.now().toString());

        return new SyncStats(downloaded, updated, skipped, failed, updatedDocumentIds);
    }

    private static CombinedBuildResult buildCombinedPdfs(
            List<DocumentRecord> documents,
            StorageEngine storageEngine,
            boolean hadDownloads,
            Set<String> updatedDocumentIds
    ) throws IOException {
        boolean hadUpdates = updatedDocumentIds != null && !updatedDocumentIds.isEmpty();
        List<DocumentRecord> pdfDocuments = new ArrayList<>();
        for (DocumentRecord document : documents) {
            if (document.isPdf()) {
                pdfDocuments.add(document);
            }
        }

        if (pdfDocuments.isEmpty()) {
            LOGGER.info("No PDF documents discovered; skipping combined PDF generation.");
            return CombinedBuildResult.none();
        }

        String combinedNewMd5 = null;
        String combinedPreviousMd5 = null;
        boolean builtCombinedNew = false;
        boolean builtCombinedPrevious = false;

        boolean combinedNewExists = storageEngine.exists(COMBINED_NEW_FILE_NAME);
        boolean shouldBuildCombinedNew = hadDownloads || hadUpdates || !combinedNewExists;
        if (shouldBuildCombinedNew) {
            List<CombinedPdfSource> newSources = collectCombinedSources(pdfDocuments, storageEngine, false, updatedDocumentIds);
            if (newSources.isEmpty()) {
                LOGGER.warning("No PDF sources available for " + COMBINED_NEW_FILE_NAME + "; skipping build.");
            } else {
                byte[] combinedNewBytes = createCombinedPdfWithToc(newSources, "Texas Rule Sets and Standards - Current");
                storageEngine.write(COMBINED_NEW_FILE_NAME, combinedNewBytes);
                combinedNewMd5 = md5Hex(combinedNewBytes);
                builtCombinedNew = true;
                LOGGER.info("Built " + COMBINED_NEW_FILE_NAME + " from " + newSources.size() + " PDF(s).");
            }
        } else {
            LOGGER.info("Skipping " + COMBINED_NEW_FILE_NAME + " rebuild; no relevant changes detected.");
            combinedNewMd5 = computeStoredMd5IfPresent(storageEngine, COMBINED_NEW_FILE_NAME);
        }

        if (hadUpdates) {
            List<CombinedPdfSource> previousSources = collectCombinedSources(
                    pdfDocuments,
                    storageEngine,
                    true,
                    updatedDocumentIds
            );
            if (previousSources.isEmpty()) {
                LOGGER.warning("No PDF sources available for " + COMBINED_PREVIOUS_FILE_NAME + "; skipping build.");
            } else {
                byte[] combinedPreviousBytes = createCombinedPdfWithToc(
                        previousSources,
                        "Texas Rule Sets and Standards - Previous"
                );
                storageEngine.write(COMBINED_PREVIOUS_FILE_NAME, combinedPreviousBytes);
                combinedPreviousMd5 = md5Hex(combinedPreviousBytes);
                builtCombinedPrevious = true;
                LOGGER.info("Built " + COMBINED_PREVIOUS_FILE_NAME + " from " + previousSources.size() + " PDF(s).");
            }
        } else {
            LOGGER.info("Skipping " + COMBINED_PREVIOUS_FILE_NAME + "; no rule-set updates detected.");
            combinedPreviousMd5 = computeStoredMd5IfPresent(storageEngine, COMBINED_PREVIOUS_FILE_NAME);
        }

        if (combinedNewMd5 == null) {
            combinedNewMd5 = computeStoredMd5IfPresent(storageEngine, COMBINED_NEW_FILE_NAME);
        }
        if (combinedPreviousMd5 == null) {
            combinedPreviousMd5 = computeStoredMd5IfPresent(storageEngine, COMBINED_PREVIOUS_FILE_NAME);
        }

        return new CombinedBuildResult(
                builtCombinedNew,
                combinedNewMd5,
                builtCombinedPrevious,
                combinedPreviousMd5
        );
    }

    private static List<CombinedPdfSource> collectCombinedSources(
            List<DocumentRecord> pdfDocuments,
            StorageEngine storageEngine,
            boolean preferPrevious,
            Set<String> updatedDocumentIds
    ) throws IOException {
        List<CombinedPdfSource> sources = new ArrayList<>();
        for (DocumentRecord document : pdfDocuments) {
            String selectedFileName = document.fileName();
            boolean shouldUsePrevious = preferPrevious
                    && updatedDocumentIds != null
                    && updatedDocumentIds.contains(document.id())
                    && document.previousFileName() != null
                    && storageEngine.exists(document.previousFileName());

            if (shouldUsePrevious) {
                selectedFileName = document.previousFileName();
            } else if (!storageEngine.exists(selectedFileName)) {
                LOGGER.warning("Missing PDF source for combined file: " + storageEngine.describeTarget(selectedFileName));
                continue;
            }

            byte[] bytes = storageEngine.read(selectedFileName);
            sources.add(new CombinedPdfSource(document.title(), selectedFileName, bytes));
        }
        return sources;
    }

    private static String computeStoredMd5IfPresent(StorageEngine storageEngine, String fileName) {
        try {
            if (!storageEngine.exists(fileName)) {
                return null;
            }
            return md5Hex(storageEngine.read(fileName));
        } catch (IOException ex) {
            LOGGER.warning("Unable to compute MD5 for " + fileName + ": " + ex.getMessage());
            return null;
        }
    }

    private static byte[] createCombinedPdfWithToc(List<CombinedPdfSource> sources, String tocTitle) throws IOException {
        List<CombinedPdfSource> validSources = new ArrayList<>();
        for (CombinedPdfSource source : sources) {
            try (PDDocument ignored = PDDocument.load(source.bytes())) {
                validSources.add(source);
            } catch (IOException ex) {
                LOGGER.warning("Skipping invalid PDF source for combine: " + source.fileName() + " (" + ex.getMessage() + ")");
            }
        }

        if (validSources.isEmpty()) {
            throw new IOException("No valid PDF sources were available for combined PDF generation.");
        }

        int tocEntriesPerPage = calculateTocEntriesPerPage(PDRectangle.LETTER);
        int tocPageCount = Math.max(1, (int) Math.ceil(validSources.size() / (double) tocEntriesPerPage));

        try (PDDocument combinedDocument = new PDDocument()) {
            List<PDDocument> openedSourceDocuments = new ArrayList<>();
            try {
                for (int i = 0; i < tocPageCount; i++) {
                    combinedDocument.addPage(new PDPage(PDRectangle.LETTER));
                }

                List<TocEntry> tocEntries = new ArrayList<>();
                for (CombinedPdfSource source : validSources) {
                    int startPageIndex = combinedDocument.getNumberOfPages();
                    PDDocument sourceDocument = PDDocument.load(source.bytes());
                    openedSourceDocuments.add(sourceDocument);
                    appendPdfPages(combinedDocument, sourceDocument);
                    tocEntries.add(new TocEntry(source.title(), startPageIndex));
                }

                writeTocPages(combinedDocument, tocEntries, tocPageCount, tocTitle);

                ByteArrayOutputStream output = new ByteArrayOutputStream();
                combinedDocument.save(output);
                return output.toByteArray();
            } finally {
                for (PDDocument sourceDocument : openedSourceDocuments) {
                    try {
                        sourceDocument.close();
                    } catch (IOException ignored) {
                    }
                }
            }
        }
    }

    private static void writeTocPages(
            PDDocument combinedDocument,
            List<TocEntry> tocEntries,
            int tocPageCount,
            String tocTitle
    ) throws IOException {
        PDType1Font titleFont = PDType1Font.HELVETICA_BOLD;
        PDType1Font entryFont = PDType1Font.HELVETICA;

        int entriesPerPage = calculateTocEntriesPerPage(PDRectangle.LETTER);
        int entryIndex = 0;
        for (int tocPageIndex = 0; tocPageIndex < tocPageCount; tocPageIndex++) {
            PDPage tocPage = combinedDocument.getPage(tocPageIndex);
            PDRectangle pageSize = tocPage.getMediaBox();
            float y = pageSize.getHeight() - TOC_PAGE_MARGIN;

            try (PDPageContentStream contentStream = new PDPageContentStream(
                    combinedDocument,
                    tocPage,
                    PDPageContentStream.AppendMode.OVERWRITE,
                    false
            )) {
                String title = tocPageIndex == 0 ? tocTitle : tocTitle + " (continued)";
                contentStream.beginText();
                contentStream.setFont(titleFont, TOC_TITLE_FONT_SIZE);
                contentStream.newLineAtOffset(TOC_PAGE_MARGIN, y);
                contentStream.showText(sanitizePdfText(title));
                contentStream.endText();
                y -= TOC_TITLE_FONT_SIZE + TOC_LINE_HEIGHT;

                for (int line = 0; line < entriesPerPage && entryIndex < tocEntries.size(); line++, entryIndex++) {
                    TocEntry entry = tocEntries.get(entryIndex);
                    String pageText = Integer.toString(entry.targetPageIndex() + 1);
                    float pageTextWidth = widthOfText(entryFont, TOC_ENTRY_FONT_SIZE, pageText);
                    float pageTextX = pageSize.getWidth() - TOC_PAGE_MARGIN - pageTextWidth;
                    float leftMaxWidth = Math.max(pageTextX - TOC_PAGE_MARGIN - 20f, 40f);
                    String leftText = truncateTextToWidth(
                            (entryIndex + 1) + ". " + entry.title(),
                            entryFont,
                            TOC_ENTRY_FONT_SIZE,
                            leftMaxWidth
                    );

                    contentStream.beginText();
                    contentStream.setFont(entryFont, TOC_ENTRY_FONT_SIZE);
                    contentStream.newLineAtOffset(TOC_PAGE_MARGIN, y);
                    contentStream.showText(leftText);
                    contentStream.endText();

                    contentStream.beginText();
                    contentStream.setFont(entryFont, TOC_ENTRY_FONT_SIZE);
                    contentStream.newLineAtOffset(pageTextX, y);
                    contentStream.showText(pageText);
                    contentStream.endText();

                    PDAnnotationLink link = new PDAnnotationLink();
                    link.setRectangle(new PDRectangle(
                            TOC_PAGE_MARGIN,
                            y - 2f,
                            pageSize.getWidth() - (TOC_PAGE_MARGIN * 2f),
                            TOC_LINE_HEIGHT
                    ));
                    PDActionGoTo action = new PDActionGoTo();
                    PDPageFitWidthDestination destination = new PDPageFitWidthDestination();
                    destination.setPage(combinedDocument.getPage(entry.targetPageIndex()));
                    action.setDestination(destination);
                    link.setAction(action);
                    tocPage.getAnnotations().add(link);

                    y -= TOC_LINE_HEIGHT;
                }
            }
        }
    }

    private static void appendPdfPages(PDDocument destination, PDDocument source) throws IOException {
        for (PDPage page : source.getPages()) {
            PDPage imported = destination.importPage(page);
            imported.setRotation(page.getRotation());
            imported.setMediaBox(page.getMediaBox());
            imported.setCropBox(page.getCropBox());
            imported.setBleedBox(page.getBleedBox());
            imported.setTrimBox(page.getTrimBox());
            imported.setArtBox(page.getArtBox());
        }
    }

    private static int calculateTocEntriesPerPage(PDRectangle pageSize) {
        float availableHeight = pageSize.getHeight()
                - (TOC_PAGE_MARGIN * 2f)
                - TOC_TITLE_FONT_SIZE
                - TOC_LINE_HEIGHT;
        int entries = (int) Math.floor(availableHeight / TOC_LINE_HEIGHT);
        return Math.max(entries, 1);
    }

    private static String sanitizePdfText(String value) {
        if (value == null) {
            return "";
        }
        return value.replaceAll("[^\\x20-\\x7E]", "?");
    }

    private static String truncateTextToWidth(String value, PDFont font, float fontSize, float maxWidth) throws IOException {
        String text = sanitizePdfText(value);
        if (widthOfText(font, fontSize, text) <= maxWidth) {
            return text;
        }

        String ellipsis = "...";
        float ellipsisWidth = widthOfText(font, fontSize, ellipsis);
        if (ellipsisWidth >= maxWidth) {
            return ellipsis;
        }

        int end = text.length();
        while (end > 0) {
            String candidate = text.substring(0, end) + ellipsis;
            if (widthOfText(font, fontSize, candidate) <= maxWidth) {
                return candidate;
            }
            end--;
        }
        return ellipsis;
    }

    private static float widthOfText(PDFont font, float fontSize, String text) throws IOException {
        return font.getStringWidth(text) / 1000f * fontSize;
    }

    private static void applyCombinedMetadata(
            Properties updatedMetadata,
            CombinedBuildResult combinedBuild,
            Properties previousMetadata
    ) {
        updatedMetadata.setProperty("combined.new.fileName", COMBINED_NEW_FILE_NAME);
        setOptionalProperty(
                updatedMetadata,
                "combined.new.md5",
                firstNonBlank(combinedBuild.combinedNewMd5(), previousMetadata.getProperty("combined.new.md5"))
        );
        setOptionalProperty(
                updatedMetadata,
                "combined.new.lastBuiltAt",
                combinedBuild.builtCombinedNew() ? Instant.now().toString() : previousMetadata.getProperty("combined.new.lastBuiltAt")
        );

        updatedMetadata.setProperty("combined.previous.fileName", COMBINED_PREVIOUS_FILE_NAME);
        setOptionalProperty(
                updatedMetadata,
                "combined.previous.md5",
                firstNonBlank(combinedBuild.combinedPreviousMd5(), previousMetadata.getProperty("combined.previous.md5"))
        );
        setOptionalProperty(
                updatedMetadata,
                "combined.previous.lastBuiltAt",
                combinedBuild.builtCombinedPrevious()
                        ? Instant.now().toString()
                        : previousMetadata.getProperty("combined.previous.lastBuiltAt")
        );
    }

    private static void extractPdfTextArtifacts(
            List<DocumentRecord> documents,
            StorageEngine storageEngine,
            Properties updatedMetadata,
            Properties previousMetadata
    ) {
        LOGGER.info("Ensuring .txt extraction artifacts for PDF files.");

        for (DocumentRecord document : documents) {
            if (!document.isPdf()) {
                continue;
            }

            String docPrefix = "doc." + document.id() + ".";
            String newPdfMd5 = updatedMetadata.getProperty(docPrefix + "md5.new");
            ensureTextArtifact(
                    storageEngine,
                    updatedMetadata,
                    previousMetadata,
                    docPrefix + "txt.new",
                    document.fileName(),
                    newPdfMd5
            );

            if (document.previousFileName() != null) {
                String previousPdfMd5 = updatedMetadata.getProperty(docPrefix + "md5.previous");
                ensureTextArtifact(
                        storageEngine,
                        updatedMetadata,
                        previousMetadata,
                        docPrefix + "txt.previous",
                        document.previousFileName(),
                        previousPdfMd5
                );
            } else {
                clearTextArtifactMetadata(updatedMetadata, docPrefix + "txt.previous");
            }
        }

        ensureTextArtifact(
                storageEngine,
                updatedMetadata,
                previousMetadata,
                "combined.new.txt",
                COMBINED_NEW_FILE_NAME,
                updatedMetadata.getProperty("combined.new.md5")
        );
        ensureTextArtifact(
                storageEngine,
                updatedMetadata,
                previousMetadata,
                "combined.previous.txt",
                COMBINED_PREVIOUS_FILE_NAME,
                updatedMetadata.getProperty("combined.previous.md5")
        );
    }

    private static void preserveTextArtifactMetadata(Properties updatedMetadata, Properties previousMetadata) {
        for (String key : previousMetadata.stringPropertyNames()) {
            if (isTextArtifactMetadataKey(key)) {
                updatedMetadata.setProperty(key, previousMetadata.getProperty(key, ""));
            }
        }
    }

    private static boolean isTextArtifactMetadataKey(String key) {
        if (key == null || key.isBlank()) {
            return false;
        }
        if (key.startsWith("combined.new.txt.") || key.startsWith("combined.previous.txt.")) {
            return true;
        }
        return key.startsWith("doc.") && (key.contains(".txt.new.") || key.contains(".txt.previous."));
    }

    private static void ensureTextArtifact(
            StorageEngine storageEngine,
            Properties updatedMetadata,
            Properties previousMetadata,
            String metadataPrefix,
            String pdfFileName,
            String pdfMd5
    ) {
        try {
            if (pdfFileName == null || pdfFileName.isBlank() || pdfMd5 == null || pdfMd5.isBlank() || !storageEngine.exists(pdfFileName)) {
                clearTextArtifactMetadata(updatedMetadata, metadataPrefix);
                return;
            }

            String textFileName = toTextFileName(pdfFileName);
            String previousSourceMd5 = previousMetadata.getProperty(metadataPrefix + ".sourceMd5");
            String previousTextMd5 = previousMetadata.getProperty(metadataPrefix + ".md5");
            String previousLastExtractedAt = previousMetadata.getProperty(metadataPrefix + ".lastExtractedAt");
            boolean needsExtraction = !storageEngine.exists(textFileName) || !pdfMd5.equals(previousSourceMd5);

            String textMd5;
            if (needsExtraction) {
                LOGGER.info("Extracting text to " + textFileName + " from " + pdfFileName);
                byte[] pdfBytes = storageEngine.read(pdfFileName);
                byte[] textBytes = extractPdfTextWithPageMarkers(pdfBytes).getBytes(StandardCharsets.UTF_8);
                storageEngine.write(textFileName, textBytes);
                textMd5 = md5Hex(textBytes);
                updatedMetadata.setProperty(metadataPrefix + ".lastExtractedAt", Instant.now().toString());
            } else {
                textMd5 = firstNonBlank(previousTextMd5, computeStoredMd5IfPresent(storageEngine, textFileName));
                setOptionalProperty(updatedMetadata, metadataPrefix + ".lastExtractedAt", previousLastExtractedAt);
            }

            updatedMetadata.setProperty(metadataPrefix + ".fileName", textFileName);
            updatedMetadata.setProperty(metadataPrefix + ".sourceMd5", pdfMd5);
            setOptionalProperty(updatedMetadata, metadataPrefix + ".md5", textMd5);
        } catch (IOException ex) {
            LOGGER.warning("Unable to extract text artifact for '" + pdfFileName + "': " + ex.getMessage());
            String previousSourceMd5 = previousMetadata.getProperty(metadataPrefix + ".sourceMd5");
            if (previousSourceMd5 != null && !previousSourceMd5.isBlank()) {
                for (String key : previousMetadata.stringPropertyNames()) {
                    if (key.startsWith(metadataPrefix + ".")) {
                        updatedMetadata.setProperty(key, previousMetadata.getProperty(key, ""));
                    }
                }
            } else {
                clearTextArtifactMetadata(updatedMetadata, metadataPrefix);
            }
        }
    }

    private static void clearTextArtifactMetadata(Properties metadata, String metadataPrefix) {
        metadata.remove(metadataPrefix + ".fileName");
        metadata.remove(metadataPrefix + ".sourceMd5");
        metadata.remove(metadataPrefix + ".md5");
        metadata.remove(metadataPrefix + ".lastExtractedAt");
    }

    private static String toTextFileName(String pdfFileName) {
        String normalized = pdfFileName.replace('\\', '/');
        while (normalized.startsWith("/")) {
            normalized = normalized.substring(1);
        }
        String lower = normalized.toLowerCase(Locale.US);
        if (lower.endsWith(".pdf")) {
            normalized = normalized.substring(0, normalized.length() - 4) + ".txt";
        } else {
            normalized = normalized + ".txt";
        }
        return TEXT_OUTPUT_DIRECTORY + "/" + normalized;
    }

    private static String extractPdfTextWithPageMarkers(byte[] pdfBytes) throws IOException {
        PDFParser parser = new PDFParser();
        StringBuilder output = new StringBuilder();

        try (PDDocument pdDocument = PDDocument.load(pdfBytes)) {
            int pageCount = pdDocument.getNumberOfPages();
            for (int page = 1; page <= pageCount; page++) {
                ParseContext parseContext = new ParseContext();
                BodyContentHandler handler = new BodyContentHandler(-1);
                Metadata metadata = new Metadata();
                byte[] singlePagePdf = extractSinglePdfPage(pdDocument, page - 1);
                try (ByteArrayInputStream input = new ByteArrayInputStream(singlePagePdf)) {
                    parser.parse(input, handler, metadata, parseContext);
                } catch (TikaException | SAXException ex) {
                    throw new IOException("Tika parsing failed for PDF page " + page, ex);
                }

                output.append("===== PDF PAGE ").append(page).append(" =====").append(System.lineSeparator());
                String pageText = normalizeExtractedText(handler.toString());
                if (pageText.isBlank()) {
                    output.append("[No extractable text]").append(System.lineSeparator());
                } else {
                    output.append(pageText).append(System.lineSeparator());
                }
                output.append(System.lineSeparator());
            }
        }

        return output.toString();
    }

    private static byte[] extractSinglePdfPage(PDDocument sourceDocument, int zeroBasedPageIndex) throws IOException {
        try (PDDocument singlePageDocument = new PDDocument()) {
            PDPage sourcePage = sourceDocument.getPage(zeroBasedPageIndex);
            PDPage imported = singlePageDocument.importPage(sourcePage);
            imported.setRotation(sourcePage.getRotation());
            imported.setMediaBox(sourcePage.getMediaBox());
            imported.setCropBox(sourcePage.getCropBox());
            imported.setBleedBox(sourcePage.getBleedBox());
            imported.setTrimBox(sourcePage.getTrimBox());
            imported.setArtBox(sourcePage.getArtBox());

            ByteArrayOutputStream output = new ByteArrayOutputStream();
            singlePageDocument.save(output);
            return output.toByteArray();
        }
    }

    private static String normalizeExtractedText(String value) {
        if (value == null) {
            return "";
        }
        String normalized = value.replace("\r\n", "\n").replace('\r', '\n').trim();
        return normalized;
    }

    private static byte[] downloadDocument(HttpClient httpClient, URI documentUri) throws IOException, InterruptedException {
        HttpRequest request = HttpRequest.newBuilder(documentUri)
                .GET()
                .timeout(Duration.ofSeconds(90))
                .header("User-Agent", HTTP_USER_AGENT)
                .header("Accept", "application/pdf,application/msword,application/vnd.openxmlformats-officedocument.wordprocessingml.document,*/*")
                .build();

        HttpResponse<byte[]> response = httpClient.send(request, HttpResponse.BodyHandlers.ofByteArray());
        int statusCode = response.statusCode();
        if (statusCode < 200 || statusCode >= 300) {
            throw new IOException("Download failed for " + documentUri + ". HTTP status " + statusCode);
        }

        byte[] body = response.body();
        if (body == null || body.length == 0) {
            throw new IOException("Download returned empty content for " + documentUri);
        }
        return body;
    }

    private static void updateMetadataEntry(
            Properties metadata,
            String metadataPrefix,
            DocumentRecord document,
            StorageEngine storageEngine,
            String md5NewChecksum,
            String md5PreviousChecksum
    ) {
        metadata.setProperty(metadataPrefix + "title", document.title());
        metadata.setProperty(metadataPrefix + "url", document.downloadUri().toString());
        metadata.setProperty(metadataPrefix + "section", document.sectionKey());
        metadata.setProperty(metadataPrefix + "fileName", document.fileName());
        setOptionalProperty(metadata, metadataPrefix + "previousFileName", document.previousFileName());
        metadata.setProperty(metadataPrefix + "storageEngine", storageEngine.name());
        metadata.setProperty(metadataPrefix + "storageTarget", storageEngine.describeTarget(document));
        metadata.setProperty(metadataPrefix + "lastAmended", safeValue(document.lastAmendedRaw()));
        setOptionalProperty(metadata, metadataPrefix + "md5.new", md5NewChecksum);
        setOptionalProperty(metadata, metadataPrefix + "md5.previous", md5PreviousChecksum);
        setOptionalProperty(metadata, metadataPrefix + "md5", md5NewChecksum);
        metadata.setProperty(metadataPrefix + "lastSyncedAt", Instant.now().toString());
        metadata.remove(metadataPrefix + "lastAttemptFailedAt");
    }

    private static void preservePreviousMetadata(
            Properties updatedMetadata,
            Properties previousMetadata,
            String metadataPrefix,
            DocumentRecord document,
            StorageEngine storageEngine
    ) {
        boolean copied = false;
        for (String key : previousMetadata.stringPropertyNames()) {
            if (key.startsWith(metadataPrefix)) {
                updatedMetadata.setProperty(key, previousMetadata.getProperty(key, ""));
                copied = true;
            }
        }

        if (!copied) {
            updatedMetadata.setProperty(metadataPrefix + "title", document.title());
            updatedMetadata.setProperty(metadataPrefix + "url", document.downloadUri().toString());
            updatedMetadata.setProperty(metadataPrefix + "section", document.sectionKey());
            updatedMetadata.setProperty(metadataPrefix + "fileName", document.fileName());
            setOptionalProperty(updatedMetadata, metadataPrefix + "previousFileName", document.previousFileName());
            updatedMetadata.setProperty(metadataPrefix + "storageEngine", storageEngine.name());
            updatedMetadata.setProperty(metadataPrefix + "storageTarget", storageEngine.describeTarget(document));
            updatedMetadata.setProperty(metadataPrefix + "lastAmended", "");
            setOptionalProperty(updatedMetadata, metadataPrefix + "md5.new", null);
            setOptionalProperty(updatedMetadata, metadataPrefix + "md5.previous", null);
            setOptionalProperty(updatedMetadata, metadataPrefix + "md5", null);
        }

        updatedMetadata.setProperty(metadataPrefix + "lastAttemptFailedAt", Instant.now().toString());
    }

    private static Element findHeadingByText(Document document, String headingText) {
        for (Element heading : document.select("h1,h2,h3,h4,h5,h6")) {
            if (normalizeWhitespace(heading.text()).equalsIgnoreCase(headingText)) {
                return heading;
            }
        }
        return null;
    }

    private static List<Element> collectSectionSiblings(Element heading) {
        List<Element> sectionSiblings = new ArrayList<>();
        int headingLevel = headingLevel(heading);
        for (Element sibling = heading.nextElementSibling(); sibling != null; sibling = sibling.nextElementSibling()) {
            if (isBoundaryHeading(sibling, headingLevel)) {
                break;
            }
            sectionSiblings.add(sibling);
        }
        return sectionSiblings;
    }

    private static void collectSectionTokens(Node node, List<SectionToken> tokens) {
        if (node instanceof Element element) {
            if ("a".equalsIgnoreCase(element.tagName()) && element.hasAttr("href")) {
                String href = element.attr("href").trim();
                String text = normalizeWhitespace(element.text());
                if (!href.isBlank()) {
                    tokens.add(SectionToken.anchor(text, href));
                }
                return;
            }
        } else if (node instanceof TextNode textNode) {
            String text = normalizeWhitespace(textNode.text());
            if (!text.isBlank()) {
                tokens.add(SectionToken.text(text));
            }
            return;
        }

        for (Node child : node.childNodes()) {
            collectSectionTokens(child, tokens);
        }
    }

    private static boolean looksLikeDocumentUrl(String href) {
        if (href == null || href.isBlank()) {
            return false;
        }
        String lower = href.toLowerCase(Locale.US);
        for (String extension : DOCUMENT_EXTENSIONS) {
            if (lower.contains("." + extension)) {
                return true;
            }
        }
        return false;
    }

    private static String inferSectionFromHtmlContext(String loweredContext) {
        int rulesIndex = loweredContext.lastIndexOf(RULES_SECTION_HEADING.toLowerCase(Locale.US));
        int standardsIndex = loweredContext.lastIndexOf(STANDARDS_SECTION_HEADING.toLowerCase(Locale.US));
        if (rulesIndex < 0 && standardsIndex < 0) {
            return null;
        }
        return standardsIndex > rulesIndex ? "standards" : "rules";
    }

    private static String findDateNearby(List<SectionToken> tokens, int anchorIndex) {
        for (int i = anchorIndex + 1; i < tokens.size(); i++) {
            SectionToken token = tokens.get(i);
            if (token.type() == TokenType.ANCHOR) {
                break;
            }
            String date = extractDateText(token.text());
            if (date != null) {
                return date;
            }
        }

        for (int i = anchorIndex - 1; i >= 0; i--) {
            SectionToken token = tokens.get(i);
            if (token.type() == TokenType.ANCHOR) {
                break;
            }
            String date = extractDateText(token.text());
            if (date != null) {
                return date;
            }
        }

        return null;
    }

    private static String extractDateText(String text) {
        if (text == null || text.isBlank()) {
            return null;
        }
        Matcher matcher = DATE_PATTERN.matcher(text);
        if (!matcher.find()) {
            return null;
        }
        return normalizeWhitespace(matcher.group());
    }

    private static LocalDate parseLastAmended(String lastAmended) {
        if (lastAmended == null || lastAmended.isBlank()) {
            return null;
        }
        try {
            return LocalDate.parse(lastAmended.trim(), LAST_AMENDED_FORMAT);
        } catch (DateTimeParseException ignored) {
            return null;
        }
    }

    private static URI resolveUri(URI baseUri, String href) {
        try {
            return baseUri.resolve(href.trim());
        } catch (Exception ex) {
            LOGGER.warning("Unable to resolve URI '" + href + "': " + ex.getMessage());
            return null;
        }
    }

    private static DocumentRecord buildDocumentRecord(
            String title,
            URI documentUri,
            String sectionKey,
            String lastAmendedRaw,
            LocalDate lastAmended
    ) {
        String extension = determineExtension(documentUri);
        String id = toSlug(sectionKey + "-" + title);
        if (id.isBlank()) {
            id = sectionKey + "-document-" + Integer.toHexString(documentUri.toString().hashCode());
        }
        String fileName;
        String previousFileName = null;
        if ("pdf".equals(extension)) {
            fileName = id + "_new.pdf";
            previousFileName = id + "_previous.pdf";
        } else {
            fileName = id + "." + extension;
        }
        return new DocumentRecord(
                id,
                normalizeWhitespace(title),
                documentUri,
                sectionKey,
                normalizeNullable(lastAmendedRaw),
                lastAmended,
                fileName,
                previousFileName
        );
    }

    private static String determineExtension(URI documentUri) {
        String path = documentUri.getPath();
        if (path == null) {
            return "pdf";
        }

        Matcher matcher = Pattern.compile("\\.([A-Za-z0-9]{2,5})$").matcher(path);
        if (!matcher.find()) {
            return "pdf";
        }

        String extension = matcher.group(1).toLowerCase(Locale.US);
        if (!DOCUMENT_EXTENSIONS.contains(extension)) {
            return "pdf";
        }
        return extension;
    }

    private static String toSlug(String value) {
        String normalized = value == null ? "" : value.toLowerCase(Locale.US);
        normalized = normalized.replaceAll("[^a-z0-9]+", "-");
        normalized = normalized.replaceAll("^-+", "");
        normalized = normalized.replaceAll("-+$", "");
        return normalized;
    }

    private static boolean isAmended(String previousRawDate, String currentRawDate, LocalDate currentDate) {
        if (currentRawDate == null || currentRawDate.isBlank()) {
            return false;
        }

        LocalDate previousDate = parseLastAmended(previousRawDate);
        if (previousDate != null && currentDate != null) {
            return !previousDate.equals(currentDate);
        }

        return !normalizeWhitespace(previousRawDate).equalsIgnoreCase(normalizeWhitespace(currentRawDate));
    }

    private static int headingLevel(Element element) {
        String tag = element.tagName().toLowerCase(Locale.US);
        if (tag.length() != 2 || tag.charAt(0) != 'h') {
            return 7;
        }
        char digit = tag.charAt(1);
        if (digit < '1' || digit > '6') {
            return 7;
        }
        return digit - '0';
    }

    private static boolean isBoundaryHeading(Element element, int startHeadingLevel) {
        int level = headingLevel(element);
        return level <= startHeadingLevel;
    }

    private static List<DocumentRecord> deduplicateDocuments(List<DocumentRecord> records) {
        Map<String, DocumentRecord> deduplicated = new LinkedHashMap<>();
        for (DocumentRecord record : records) {
            DocumentRecord existing = deduplicated.get(record.id());
            if (existing == null) {
                deduplicated.put(record.id(), record);
                continue;
            }
            if (existing.lastAmended() == null && record.lastAmended() != null) {
                deduplicated.put(record.id(), record);
            }
        }
        return new ArrayList<>(deduplicated.values());
    }

    private static int countDocumentIds(Properties metadata) {
        String trackedIds = metadata.getProperty("tracked.ids");
        if (trackedIds == null || trackedIds.isBlank()) {
            return 0;
        }
        String[] parts = trackedIds.split(",");
        int count = 0;
        for (String part : parts) {
            if (!part.isBlank()) {
                count++;
            }
        }
        return count;
    }

    private static String normalizeWhitespace(String value) {
        if (value == null) {
            return "";
        }
        return value.replaceAll("\\s+", " ").trim();
    }

    private static String normalizeNullable(String value) {
        String normalized = normalizeWhitespace(value);
        return normalized.isBlank() ? null : normalized;
    }

    private static String safeValue(String value) {
        return value == null ? "" : value;
    }

    private static String firstNonBlank(String... values) {
        if (values == null) {
            return null;
        }
        for (String value : values) {
            if (value != null && !value.isBlank()) {
                return value;
            }
        }
        return null;
    }

    private static String md5Hex(byte[] bytes) {
        try {
            MessageDigest digest = MessageDigest.getInstance("MD5");
            byte[] hash = digest.digest(bytes);
            return HexFormat.of().formatHex(hash);
        } catch (NoSuchAlgorithmException ex) {
            throw new IllegalStateException("MD5 digest is unavailable.", ex);
        }
    }

    private static void setOptionalProperty(Properties properties, String key, String value) {
        if (value == null || value.isBlank()) {
            properties.remove(key);
        } else {
            properties.setProperty(key, value);
        }
    }

    private static String normalizeStorageEngine(String value) {
        if (value == null || value.isBlank()) {
            return STORAGE_ENGINE_LOCAL;
        }
        return value.trim().toLowerCase(Locale.US);
    }

    private static String readConfig(String propertyKey, String envKey, String defaultValue) {
        String propertyValue = System.getProperty(propertyKey);
        if (propertyValue != null && !propertyValue.isBlank()) {
            return propertyValue.trim();
        }
        String envValue = System.getenv(envKey);
        if (envValue != null && !envValue.isBlank()) {
            return envValue.trim();
        }
        return defaultValue;
    }

    private static String readRequiredConfig(String propertyKey, String envKey) {
        String value = readConfig(propertyKey, envKey, null);
        if (value == null || value.isBlank()) {
            throw new IllegalArgumentException(
                    "Missing required setting '" + propertyKey + "' (or environment variable '" + envKey + "').");
        }
        return value;
    }

    private static int parsePositiveInt(String rawValue, String settingLabel) {
        if (rawValue == null || rawValue.isBlank()) {
            throw new IllegalArgumentException("Setting '" + settingLabel + "' cannot be empty.");
        }
        try {
            int parsed = Integer.parseInt(rawValue.trim());
            if (parsed <= 0) {
                throw new IllegalArgumentException("Setting '" + settingLabel + "' must be greater than zero.");
            }
            return parsed;
        } catch (NumberFormatException ex) {
            throw new IllegalArgumentException("Setting '" + settingLabel + "' must be an integer. Got: " + rawValue, ex);
        }
    }

    private static boolean parseBooleanConfig(String rawValue, String settingLabel) {
        if (rawValue == null || rawValue.isBlank()) {
            throw new IllegalArgumentException("Setting '" + settingLabel + "' cannot be empty.");
        }
        String normalized = rawValue.trim().toLowerCase(Locale.US);
        if ("true".equals(normalized) || "1".equals(normalized) || "yes".equals(normalized) || "on".equals(normalized)) {
            return true;
        }
        if ("false".equals(normalized) || "0".equals(normalized) || "no".equals(normalized) || "off".equals(normalized)) {
            return false;
        }
        throw new IllegalArgumentException(
                "Setting '" + settingLabel + "' must be one of: true,false,1,0,yes,no,on,off. Got: " + rawValue);
    }

    private static String normalizeRemoteDirectory(String remoteDirectory) {
        if (remoteDirectory == null || remoteDirectory.isBlank()) {
            return "/";
        }
        String normalized = remoteDirectory.trim().replace('\\', '/');
        if (!normalized.startsWith("/")) {
            normalized = "/" + normalized;
        }
        normalized = normalized.replaceAll("/+", "/");
        if (normalized.length() > 1 && normalized.endsWith("/")) {
            normalized = normalized.substring(0, normalized.length() - 1);
        }
        return normalized;
    }

    private static String normalizeWebDavBaseUrl(String baseUrl) {
        if (baseUrl == null || baseUrl.isBlank()) {
            throw new IllegalArgumentException("storage.webdav.baseUrl/WEBDAV_BASE_URL cannot be empty.");
        }
        String normalized = baseUrl.trim();
        if (!(normalized.startsWith("http://") || normalized.startsWith("https://"))) {
            throw new IllegalArgumentException(
                    "storage.webdav.baseUrl/WEBDAV_BASE_URL must start with http:// or https://");
        }
        while (normalized.endsWith("/")) {
            normalized = normalized.substring(0, normalized.length() - 1);
        }
        return normalized;
    }

    private static boolean isNoSuchFileError(SftpException exception) {
        return exception.id == ChannelSftp.SSH_FX_NO_SUCH_FILE;
    }

    private interface StorageEngine extends AutoCloseable {

        String name();

        String describeRoot();

        String describeTarget(String fileName);

        boolean exists(String fileName) throws IOException;

        byte[] read(String fileName) throws IOException;

        void write(String fileName, byte[] bytes) throws IOException;

        default String describeTarget(DocumentRecord document) {
            return describeTarget(document.fileName());
        }

        default boolean exists(DocumentRecord document) throws IOException {
            return exists(document.fileName());
        }

        default void preservePrevious(DocumentRecord document) throws IOException {
            if (document.previousFileName() == null || !exists(document.fileName())) {
                return;
            }
            write(document.previousFileName(), read(document.fileName()));
        }

        default void write(DocumentRecord document, byte[] bytes) throws IOException {
            write(document.fileName(), bytes);
        }

        @Override
        default void close() throws IOException {
        }
    }

    private static final class LocalStorageEngine implements StorageEngine {

        private final Path rootDirectory;

        private LocalStorageEngine(Path rootDirectory) throws IOException {
            this.rootDirectory = rootDirectory;
            Files.createDirectories(rootDirectory);
        }

        @Override
        public String name() {
            return STORAGE_ENGINE_LOCAL;
        }

        @Override
        public String describeRoot() {
            return rootDirectory.toAbsolutePath().toString();
        }

        @Override
        public String describeTarget(String fileName) {
            return rootDirectory.resolve(fileName).toAbsolutePath().toString();
        }

        @Override
        public boolean exists(String fileName) {
            return Files.exists(rootDirectory.resolve(fileName));
        }

        @Override
        public byte[] read(String fileName) throws IOException {
            return Files.readAllBytes(rootDirectory.resolve(fileName));
        }

        @Override
        public void write(String fileName, byte[] bytes) throws IOException {
            Path destinationPath = rootDirectory.resolve(fileName);
            Path parentDirectory = destinationPath.getParent();
            if (parentDirectory != null) {
                Files.createDirectories(parentDirectory);
            }
            Path tempFile = Files.createTempFile(rootDirectory, "rules-standards-", ".tmp");
            try {
                Files.write(tempFile, bytes, StandardOpenOption.TRUNCATE_EXISTING);
                try {
                    Files.move(tempFile, destinationPath, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE);
                } catch (AtomicMoveNotSupportedException ignored) {
                    Files.move(tempFile, destinationPath, StandardCopyOption.REPLACE_EXISTING);
                }
            } finally {
                Files.deleteIfExists(tempFile);
            }
        }
    }

    private static final class SftpStorageEngine implements StorageEngine {

        private final StorageSettings settings;
        private final Session session;
        private final ChannelSftp channel;
        private final String remoteRoot;

        private SftpStorageEngine(StorageSettings settings) throws IOException {
            this.settings = settings;

            Session connectedSession = null;
            ChannelSftp connectedChannel = null;
            String connectedRemoteRoot = null;

            try {
                JSch jsch = new JSch();
                connectedSession = jsch.getSession(settings.sftpUsername(), settings.sftpHost(), settings.sftpPort());
                connectedSession.setPassword(settings.sftpPassword());

                Properties sessionConfig = new Properties();
                sessionConfig.setProperty("StrictHostKeyChecking", "no");
                connectedSession.setConfig(sessionConfig);
                int timeoutMillis = settings.sftpTimeoutSeconds() * 1_000;
                connectedSession.connect(timeoutMillis);

                connectedChannel = (ChannelSftp) connectedSession.openChannel("sftp");
                connectedChannel.connect(timeoutMillis);
                connectedRemoteRoot = ensureRemoteDirectory(connectedChannel, settings.sftpRemoteDir());
            } catch (JSchException | SftpException ex) {
                if (connectedChannel != null) {
                    connectedChannel.disconnect();
                }
                if (connectedSession != null) {
                    connectedSession.disconnect();
                }
                throw new IOException("Unable to initialize SFTP storage engine.", ex);
            }

            this.session = connectedSession;
            this.channel = connectedChannel;
            this.remoteRoot = connectedRemoteRoot;
        }

        @Override
        public String name() {
            return STORAGE_ENGINE_SFTP;
        }

        @Override
        public String describeRoot() {
            return settings.sftpEndpoint();
        }

        @Override
        public String describeTarget(String fileName) {
            return "sftp://" + settings.sftpHost() + ":" + settings.sftpPort() + remotePath(fileName);
        }

        @Override
        public boolean exists(String fileName) throws IOException {
            try {
                channel.lstat(remotePath(fileName));
                return true;
            } catch (SftpException ex) {
                if (isNoSuchFileError(ex)) {
                    return false;
                }
                throw new IOException("Unable to check remote file existence.", ex);
            }
        }

        @Override
        public byte[] read(String fileName) throws IOException {
            try {
                return readRemoteFile(remotePath(fileName));
            } catch (SftpException ex) {
                throw new IOException("Unable to read SFTP file '" + fileName + "'.", ex);
            }
        }

        @Override
        public void write(String fileName, byte[] bytes) throws IOException {
            String targetPath = remotePath(fileName);
            String parentDirectoryPath = parentDirectory(targetPath);
            String tempPath = targetPath + ".tmp-" + Instant.now().toEpochMilli();
            try {
                ensureRemoteDirectory(channel, parentDirectoryPath);
            } catch (SftpException ex) {
                throw new IOException("Unable to create remote directory '" + parentDirectoryPath + "'.", ex);
            }
            try (ByteArrayInputStream input = new ByteArrayInputStream(bytes)) {
                channel.put(input, tempPath, ChannelSftp.OVERWRITE);
                try {
                    channel.rm(targetPath);
                } catch (SftpException ex) {
                    if (!isNoSuchFileError(ex)) {
                        throw ex;
                    }
                }
                channel.rename(tempPath, targetPath);
            } catch (SftpException ex) {
                cleanupTempFile(tempPath);
                throw new IOException("Unable to write remote file '" + targetPath + "'.", ex);
            }
        }

        @Override
        public void close() {
            if (channel != null && channel.isConnected()) {
                channel.disconnect();
            }
            if (session != null && session.isConnected()) {
                session.disconnect();
            }
        }

        private String remotePath(String fileName) {
            if ("/".equals(remoteRoot)) {
                return "/" + fileName;
            }
            return remoteRoot + "/" + fileName;
        }

        private byte[] readRemoteFile(String remoteFilePath) throws SftpException {
            ByteArrayOutputStream output = new ByteArrayOutputStream();
            channel.get(remoteFilePath, output);
            return output.toByteArray();
        }

        private void cleanupTempFile(String tempPath) {
            try {
                channel.rm(tempPath);
            } catch (SftpException ignored) {
            }
        }

        private static String parentDirectory(String absolutePath) {
            int index = absolutePath.lastIndexOf('/');
            if (index <= 0) {
                return "/";
            }
            return absolutePath.substring(0, index);
        }

        private static String ensureRemoteDirectory(ChannelSftp channel, String remoteDirectory) throws SftpException {
            String normalized = normalizeRemoteDirectory(remoteDirectory);
            channel.cd("/");
            if ("/".equals(normalized)) {
                return normalized;
            }

            String[] parts = normalized.substring(1).split("/");
            for (String part : parts) {
                if (part.isBlank()) {
                    continue;
                }
                try {
                    channel.cd(part);
                } catch (SftpException ex) {
                    if (!isNoSuchFileError(ex)) {
                        throw ex;
                    }
                    channel.mkdir(part);
                    channel.cd(part);
                }
            }
            return normalized;
        }
    }

    private static final class WebDavStorageEngine implements StorageEngine {

        private final StorageSettings settings;
        private final HttpClient httpClient;
        private final String baseUrl;
        private final String remoteRoot;
        private final String authorizationHeader;
        private final Duration timeout;

        private WebDavStorageEngine(StorageSettings settings) throws IOException {
            this.settings = settings;
            this.baseUrl = normalizeWebDavBaseUrl(settings.webDavBaseUrl());
            this.remoteRoot = normalizeRemoteDirectory(settings.webDavRemoteDir());
            this.timeout = Duration.ofSeconds(settings.webDavTimeoutSeconds());
            this.authorizationHeader = basicAuthHeader(settings.webDavUsername(), settings.webDavPassword());
            this.httpClient = HttpClient.newBuilder()
                    .followRedirects(HttpClient.Redirect.NORMAL)
                    .connectTimeout(this.timeout)
                    .build();

            ensureRemoteDirectoryExists();
        }

        @Override
        public String name() {
            return STORAGE_ENGINE_WEBDAV;
        }

        @Override
        public String describeRoot() {
            return settings.webDavEndpoint();
        }

        @Override
        public String describeTarget(String fileName) {
            return urlForPath(remotePath(fileName));
        }

        @Override
        public boolean exists(String fileName) throws IOException {
            String targetUrl = urlForPath(remotePath(fileName));
            int statusCode = sendWithoutBody("HEAD", targetUrl, false);
            if (isSuccessStatus(statusCode)) {
                return true;
            }
            if (statusCode == 404) {
                return false;
            }
            if (statusCode == 405) {
                int fallback = sendWithoutBody("PROPFIND", targetUrl, true);
                if (isSuccessStatus(fallback) || fallback == 207) {
                    return true;
                }
                if (fallback == 404) {
                    return false;
                }
                throw new IOException("WebDAV PROPFIND failed with HTTP status " + fallback + " for " + targetUrl);
            }
            throw new IOException("WebDAV HEAD failed with HTTP status " + statusCode + " for " + targetUrl);
        }

        @Override
        public byte[] read(String fileName) throws IOException {
            String url = urlForPath(remotePath(fileName));
            HttpResponse<byte[]> response = sendRead("GET", url);
            int statusCode = response.statusCode();
            if (!isSuccessStatus(statusCode)) {
                throw new IOException("WebDAV GET failed with HTTP status " + statusCode + " for " + url);
            }
            return response.body();
        }

        @Override
        public void write(String fileName, byte[] bytes) throws IOException {
            String targetPath = remotePath(fileName);
            ensureDirectoryPathExists(parentDirectory(targetPath));
            String targetUrl = urlForPath(targetPath);
            int statusCode = sendWithBody("PUT", targetUrl, bytes);
            if (!isSuccessStatus(statusCode)) {
                throw new IOException("WebDAV PUT failed with HTTP status " + statusCode + " for " + targetUrl);
            }
        }

        private void ensureRemoteDirectoryExists() throws IOException {
            ensureDirectoryPathExists(remoteRoot);
        }

        private void ensureDirectoryPathExists(String absoluteDirectoryPath) throws IOException {
            if (absoluteDirectoryPath == null || absoluteDirectoryPath.isBlank() || "/".equals(absoluteDirectoryPath)) {
                return;
            }

            String[] parts = absoluteDirectoryPath.substring(1).split("/");
            StringBuilder currentPath = new StringBuilder();
            for (String part : parts) {
                if (part.isBlank()) {
                    continue;
                }
                currentPath.append('/').append(part);
                int statusCode = sendWithoutBody("MKCOL", urlForPath(currentPath + "/"), false);
                if (statusCode == 201 || statusCode == 405 || statusCode == 301 || statusCode == 302
                        || statusCode == 307 || statusCode == 308 || isSuccessStatus(statusCode)) {
                    continue;
                }
                throw new IOException(
                        "WebDAV MKCOL failed with HTTP status " + statusCode + " while creating " + currentPath);
            }
        }

        private static String parentDirectory(String absolutePath) {
            int index = absolutePath.lastIndexOf('/');
            if (index <= 0) {
                return "/";
            }
            return absolutePath.substring(0, index);
        }

        private int sendWithoutBody(String method, String url, boolean propfindDepthZero) throws IOException {
            HttpRequest.Builder builder = requestBuilder(url);
            if (propfindDepthZero) {
                builder.header("Depth", "0");
            }
            HttpRequest request = builder
                    .method(method, HttpRequest.BodyPublishers.noBody())
                    .build();
            try {
                HttpResponse<Void> response = httpClient.send(request, HttpResponse.BodyHandlers.discarding());
                return response.statusCode();
            } catch (InterruptedException ex) {
                Thread.currentThread().interrupt();
                throw new IOException("Interrupted during WebDAV request.", ex);
            }
        }

        private HttpResponse<byte[]> sendRead(String method, String url) throws IOException {
            HttpRequest request = requestBuilder(url)
                    .method(method, HttpRequest.BodyPublishers.noBody())
                    .build();
            try {
                return httpClient.send(request, HttpResponse.BodyHandlers.ofByteArray());
            } catch (InterruptedException ex) {
                Thread.currentThread().interrupt();
                throw new IOException("Interrupted during WebDAV read request.", ex);
            }
        }

        private int sendWithBody(String method, String url, byte[] body) throws IOException {
            HttpRequest request = requestBuilder(url)
                    .header("Content-Type", "application/octet-stream")
                    .method(method, HttpRequest.BodyPublishers.ofByteArray(body))
                    .build();
            try {
                HttpResponse<Void> response = httpClient.send(request, HttpResponse.BodyHandlers.discarding());
                return response.statusCode();
            } catch (InterruptedException ex) {
                Thread.currentThread().interrupt();
                throw new IOException("Interrupted during WebDAV upload.", ex);
            }
        }

        private HttpRequest.Builder requestBuilder(String url) throws IOException {
            URI uri;
            try {
                uri = URI.create(url);
            } catch (IllegalArgumentException ex) {
                throw new IOException("Invalid WebDAV URL: " + url, ex);
            }

            return HttpRequest.newBuilder(uri)
                    .timeout(timeout)
                    .header("Authorization", authorizationHeader)
                    .header("Accept", "*/*");
        }

        private String remotePath(String fileName) {
            if ("/".equals(remoteRoot)) {
                return "/" + fileName;
            }
            return remoteRoot + "/" + fileName;
        }

        private String urlForPath(String path) {
            return baseUrl + path;
        }

        private static String basicAuthHeader(String username, String password) {
            String credentials = username + ":" + password;
            String encoded = Base64.getEncoder().encodeToString(credentials.getBytes(StandardCharsets.UTF_8));
            return "Basic " + encoded;
        }

        private static boolean isSuccessStatus(int statusCode) {
            return statusCode >= 200 && statusCode < 300;
        }
    }

    private record CombinedBuildResult(
            boolean builtCombinedNew,
            String combinedNewMd5,
            boolean builtCombinedPrevious,
            String combinedPreviousMd5
    ) {

        private static CombinedBuildResult none() {
            return new CombinedBuildResult(false, null, false, null);
        }
    }

    private record CombinedPdfSource(String title, String fileName, byte[] bytes) {
    }

    private record TocEntry(String title, int targetPageIndex) {
    }

    private record SyncStats(
            int downloaded,
            int updated,
            int skipped,
            int failed,
            Set<String> updatedDocumentIds
    ) {
    }

    private record StorageSettings(
            String engine,
            String sftpHost,
            int sftpPort,
            String sftpUsername,
            String sftpPassword,
            String sftpRemoteDir,
            int sftpTimeoutSeconds,
            String webDavBaseUrl,
            String webDavUsername,
            String webDavPassword,
            String webDavRemoteDir,
            int webDavTimeoutSeconds
    ) {

        private static StorageSettings local() {
            return new StorageSettings(
                    STORAGE_ENGINE_LOCAL,
                    null,
                    22,
                    null,
                    null,
                    "/",
                    30,
                    null,
                    null,
                    null,
                    "/",
                    30
            );
        }

        private static StorageSettings sftp(
                String host,
                int port,
                String username,
                String password,
                String remoteDir,
                int timeoutSeconds
        ) {
            return new StorageSettings(
                    STORAGE_ENGINE_SFTP,
                    host,
                    port,
                    username,
                    password,
                    remoteDir,
                    timeoutSeconds,
                    null,
                    null,
                    null,
                    "/",
                    30
            );
        }

        private static StorageSettings webDav(
                String baseUrl,
                String username,
                String password,
                String remoteDir,
                int timeoutSeconds
        ) {
            return new StorageSettings(
                    STORAGE_ENGINE_WEBDAV,
                    null,
                    22,
                    null,
                    null,
                    "/",
                    30,
                    baseUrl,
                    username,
                    password,
                    remoteDir,
                    timeoutSeconds
            );
        }

        private String sftpEndpoint() {
            return "sftp://" + sftpHost + ":" + sftpPort + sftpRemoteDir;
        }

        private String webDavEndpoint() {
            return webDavBaseUrl + webDavRemoteDir;
        }
    }

    private record DocumentRecord(
            String id,
            String title,
            URI downloadUri,
            String sectionKey,
            String lastAmendedRaw,
            LocalDate lastAmended,
            String fileName,
            String previousFileName
    ) {

        private boolean isPdf() {
            return fileName != null && fileName.toLowerCase(Locale.US).endsWith(".pdf");
        }
    }

    private enum TokenType {
        ANCHOR,
        TEXT
    }

    private record SectionToken(TokenType type, String text, String href) {
        private static SectionToken anchor(String text, String href) {
            return new SectionToken(TokenType.ANCHOR, text, href);
        }

        private static SectionToken text(String text) {
            return new SectionToken(TokenType.TEXT, text, null);
        }
    }

    private static final class SimpleLogFormatter extends Formatter {

        @Override
        public String format(LogRecord record) {
            Instant instant = Instant.ofEpochMilli(record.getMillis());
            String timestamp = DateTimeFormatter.ofPattern("uuuu-MM-dd HH:mm:ss")
                    .withZone(ZoneId.systemDefault())
                    .format(instant);

            StringBuilder output = new StringBuilder();
            output.append(timestamp)
                    .append(" [")
                    .append(record.getLevel().getName())
                    .append("] ")
                    .append(formatMessage(record))
                    .append(System.lineSeparator());

            Throwable thrown = record.getThrown();
            if (thrown != null) {
                output.append("  cause: ").append(thrown).append(System.lineSeparator());
                for (StackTraceElement element : thrown.getStackTrace()) {
                    output.append("    at ").append(element).append(System.lineSeparator());
                }
            }
            return output.toString();
        }
    }
}
