package de.intranda.utils;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.NotSerializableException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.io.UnsupportedEncodingException;
import java.text.DateFormat;
import java.text.DecimalFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Date;
import java.util.GregorianCalendar;
import java.util.List;
import java.util.Scanner;
import java.util.TimeZone;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import org.apache.commons.io.output.FileWriterWithEncoding;
import org.apache.log4j.Logger;
import org.jdom.Document;
import org.jdom.JDOMException;
import org.jdom.input.SAXBuilder;
import org.jdom.output.Format;
import org.jdom.output.XMLOutputter;

/**
 * Collection of common all-purpose functions
 * 
 * 
 * @author florian
 * 
 */
public class CommonUtils {

	/** Logger for this class. */
	private static final Logger logger = Logger.getLogger(CommonUtils.class);
	public static final String encoding = "utf-8"; // "iso-8859-15"
	public static final String lineSeparator = "\n";

	/**
	 * Writing serializable objects to a file
	 * 
	 * @param file
	 * @param obj
	 */
	public static void writeFile(File file, Object obj) {
		try {
			FileOutputStream fs = new FileOutputStream(file);
			ObjectOutputStream os = new ObjectOutputStream(fs);
			os.writeObject(obj);
			os.close();
		} catch (IOException e) {
			logger.error("Error writing binary file", e);
		}
	}

	/**
	 * Reading serializable objects from a file
	 * 
	 * @param file
	 * @return
	 */
	public static Object readFile(File file) {
		FileInputStream fis;
		Object obj = null;
		try {
			fis = new FileInputStream(file);
			ObjectInputStream ois = new ObjectInputStream(fis);
			obj = ois.readObject();
			ois.close();
		} catch (FileNotFoundException e) {
			logger.warn("No binary file exists to read. Aborting.");
		} catch (IOException e) {
			logger.error("Error reading binary file", e);
		} catch (ClassNotFoundException e) {
			logger.error("Error reading object from binary file", e);
		}
		return obj;
	}

	/**
	 * Read a text file and return content as String
	 * 
	 * @param file
	 * @param encoding
	 *            The character encoding to use. If null, a standard utf-8 encoding will be used
	 * @return
	 */
	public static String readTextFile(File file, String encoding) {
		String result = "";

		if (encoding == null)
			encoding = CommonUtils.encoding;

		Scanner scanner = null;
		StringBuilder text = new StringBuilder();
		String NL = System.getProperty("line.separator");
		try {
			scanner = new Scanner(new FileInputStream(file), encoding);
			while (scanner.hasNextLine()) {
				text.append(scanner.nextLine() + NL);
			}
		} catch (FileNotFoundException e) {
			logger.error(e.toString());
		} finally {
			scanner.close();
		}
		result = text.toString();
		return result.trim();
	}

	public static String readByteArray(byte[] bytes, String encoding) {
		String result = "";

		if (encoding == null)
			encoding = CommonUtils.encoding;

		Scanner scanner = null;
		StringBuilder text = new StringBuilder();
		String NL = System.getProperty("line.separator");
		try {
			scanner = new Scanner(new ByteArrayInputStream(bytes), encoding);
			while (scanner.hasNextLine()) {
				text.append(scanner.nextLine() + NL);
			}
		} finally {
			scanner.close();
		}
		result = text.toString();
		return result.trim();
	}

	/**
	 * Simply write a String into a text file.
	 * 
	 * @param string
	 *            The String to write
	 * @param file
	 *            The file to write to (will be created if it doesn't exist
	 * @param encoding
	 *            The character encoding to use. If null, a standard utf-8 encoding will be used
	 * @param append
	 *            Whether to append the text to an existing file (true), or to overwrite it (false)
	 * @return
	 * @throws IOException
	 */
	public static File writeTextFile(String string, File file, String encoding, boolean append) throws IOException {

		if (encoding == null)
			encoding = CommonUtils.encoding;

		FileWriterWithEncoding writer = null;
		writer = new FileWriterWithEncoding(file, encoding, append);
		writer.write(string);
		if (writer != null)
			writer.close();

		return file;
	}

	/**
	 * Writes the Document doc into an xml File file
	 * 
	 * @param file
	 * @param doc
	 * @throws IOException
	 */
	public static void getFileFromDocument(File file, Document doc) throws IOException {
		writeTextFile(getStringFromDocument(doc, encoding), file, encoding, false);
	}

	/**
	 * 
	 * Creates a single String out of the Document document
	 * 
	 * @param document
	 * @param encoding
	 *            The character encoding to use. If null, a standard utf-8 encoding will be used
	 * @return
	 */
	public static String getStringFromDocument(Document document, String encoding) {
		if (document == null) {
			logger.warn("Trying to convert null document to String. Aborting");
			return null;
		}
		if (encoding == null)
			encoding = CommonUtils.encoding;

		XMLOutputter outputter = new XMLOutputter();
		Format xmlFormat = outputter.getFormat();
		if (!(encoding == null) && !encoding.isEmpty())
			xmlFormat.setEncoding(encoding);
		// xmlFormat.setOmitDeclaration(true);
		xmlFormat.setExpandEmptyElements(true);
		outputter.setFormat(xmlFormat);
		String docString = outputter.outputString(document);

		return docString;
	}

	/**
	 * Load a jDOM document from an xml file
	 * 
	 * @param file
	 * @return
	 * @throws IOException
	 * @throws JDOMException
	 */
	public static Document getDocumentFromFile(File file) throws JDOMException, IOException {
		SAXBuilder builder = new SAXBuilder(false);
		Document document = null;

		document = builder.build(file);

		return document;
	}

	/**
	 * Create a jDOM document from an xml string
	 * 
	 * @param string
	 * @return
	 */
	public static Document getDocumentFromString(String string) {
		byte[] byteArray = null;
		try {
			byteArray = string.getBytes(encoding);
		} catch (UnsupportedEncodingException e1) {
		}
		ByteArrayInputStream baos = new ByteArrayInputStream(byteArray);

		// Reader reader = new StringReader(hOCRText);
		SAXBuilder builder = new SAXBuilder(false);
		Document document = null;

		try {
			document = builder.build(baos);
		} catch (JDOMException e) {
			System.err.println("error " + e.toString());
			return null;
		} catch (IOException e) {
			System.err.println(e.toString());
			return null;
		}
		return document;
	}

	/**
	 * Moves a file to another directory, either by renaming it, or, failing that, by copying it and deleting the old file.
	 * 	 * 
	 * @param sourceFile	The file to be moved
	 * @param destFile		The path to move the file to. If this denotes an existing directory, the file will be moved into this directory under the original filename		
	 * @param force		Overwrites any possibly existing old file, and creates directories if necessary
	 * @return
	 */
	public static void moveFile(File sourceFile, File destFile, boolean force)  throws FileNotFoundException, IOException {
		
		String destFileName = null;
		File destDir = null;
		
		if(sourceFile == null || !sourceFile.isFile()) {
			throw new FileNotFoundException("Invalid source file specified");
		}
		
		if(destFile == null) {
			throw new FileNotFoundException("Invalid destination file specified");
		}
		
		if(destFile.isDirectory()) {
			destDir = destFile;
			destFileName = sourceFile.getName();
		} else {
			destDir = destFile.getParentFile();
			destFileName = destFile.getName();
		}
		
		if(destDir == null || !destDir.isDirectory()) {
			if(!force) {
				throw new FileNotFoundException("Invalid destination directory specified");
			} else if(!destDir.mkdirs()) {
				throw new IOException("Unable to create destination file");
			}
		} 
		
		File targetFile = new File(destDir, destFileName);
		if(targetFile.isFile() && !force) {
			throw new IOException("Destination file already exists");
		} else {
			if(!sourceFile.renameTo(targetFile)) {
				//renaming failed, try copying and deleting
				if(targetFile.isFile()) {
					if(!targetFile.delete()) {
						throw new IOException("Unable to overwrite destination file");
					}
				}
				copyFile(sourceFile, targetFile);
				if(targetFile.exists()) {
					sourceFile.delete();
				} else {
					throw new IOException("Copy operation failed");
				}
			}
		}
	}
	
	/**
	 * Moves (either by simply renaming or by copy and delete) all files (and directories) within directory dir to another directory destDir
	 * 
	 * @param sourcedir
	 * @param destDir
	 * @param overwrite
	 *            Forces files that are already in the destDir to be overwritten by the corresponding file in sourceDir. If false, the file will not
	 *            be moved an remain in the sourceDir
	 * @return
	 */
	public static void moveDir(File sourcedir, File destDir, boolean overwrite) throws FileNotFoundException, IOException {
		if (sourcedir == null || !sourcedir.isDirectory()) {
			throw new FileNotFoundException("Cannot move from a nonexisting directory");
		}
		if (destDir.getAbsolutePath().startsWith(sourcedir.getAbsolutePath())) {
			throw new IOException("Cannot move into its own subdirectory");
		}
		File[] files = sourcedir.listFiles();

		if (files == null || files.length == 0) {

			// don't move if destDir already exists - the source Dir is empty anyway
			if (destDir != null && destDir.isDirectory()) {
				sourcedir.delete();
				return;
			}

			boolean success = false;
			try {
				success = sourcedir.renameTo(destDir);
			} catch (NullPointerException e) {
				throw new FileNotFoundException(e.getMessage());
			}
			if (!success) {
				if(destDir.mkdir()) {
					sourcedir.delete();
				} else {
				throw new IOException("Failed moving directory " + sourcedir.getAbsolutePath());
				}
			}
			return;
		}

		if(!destDir.mkdirs()) {
			throw new IOException("Failed creating destination directories");
		}
		for (File file : files) {
			if (file.isDirectory()) {
				moveDir(file, new File(destDir, file.getName()), overwrite);
			} else {
				File destFile = new File(destDir, file.getName());
				if (overwrite || !destFile.isFile()) {
					
					try {
						moveFile(file, destDir, overwrite);
					} catch(IOException e) {
						throw new IOException("Unable to move file " + file.getAbsolutePath() + " to directory " + destDir.getAbsolutePath());
					}				
//					if (!file.renameTo(new File(destDir, file.getName()))) {
//						throw new IOException("Unable to move file " + file.getAbsolutePath() + " to directory " + destDir.getAbsolutePath());
//
//					}
				}
			}
		}
		if(sourcedir.listFiles().length == 0) {
			sourcedir.delete();
		}
		return;
	}

	/**
	 * Deletes a directory with all included files and subdirectories. If the argument is a file, it will simply delete this
	 * 
	 * @param dir
	 */
	public static boolean deleteAllFiles(File dir) {
		if (dir == null) {
			return false;
		}
		if (dir.isFile()) {
			logger.error("Unable to delete directory " + dir.getAbsolutePath());
			return dir.delete();
		}
		boolean success = true;
		if (dir.isDirectory()) {
			File[] fileList = dir.listFiles();
			if (fileList != null) {
				for (File file : fileList) {
					if (file.isDirectory()) {
						if (!deleteAllFiles(file)) {
							logger.error("Unable to delete directory " + file.getAbsolutePath());
							success = false;
						}

					} else {
						if (!file.delete()) {
							logger.error("Unable to delete directory " + file.getAbsolutePath());
							success = false;
						}
					}
				}
			}
			if (!dir.delete()) {
				logger.error("Unable to delete directory " + dir.getAbsolutePath());
				success = false;
			}
		}
		return success;
	}

	/**
	 * Copies the content of file source to file dest
	 * 
	 * @param source
	 * @param dest
	 * @throws IOException
	 */
	public static void copyFile(File source, File dest) throws IOException {

		if (!dest.exists()) {
			dest.createNewFile();
		}
		InputStream in = null;
		OutputStream out = null;
		try {
			in = new FileInputStream(source);
			out = new FileOutputStream(dest);

			// Transfer bytes from in to out
			byte[] buf = new byte[1024];
			int len;
			while ((len = in.read(buf)) > 0) {
				out.write(buf, 0, len);
			}
		} finally {
			in.close();
			out.close();
		}
	}

	/**
	 * Unzip a zip archive and write results into Array of Strings
	 * 
	 * @param source
	 * @return
	 * @throws IOException
	 */
	public static ArrayList<File> unzipFile(File source, File destDir) throws IOException {
		ArrayList<File> fileList = new ArrayList<File>();

		if (!destDir.isDirectory())
			destDir.mkdirs();

		ZipInputStream in = null;
		try {
			in = new ZipInputStream((new BufferedInputStream(new FileInputStream(source))));
			ZipEntry entry;
			while ((entry = in.getNextEntry()) != null) {
				File tempFile = new File(destDir, entry.getName());
				fileList.add(tempFile);
				tempFile.getParentFile().mkdirs();
				tempFile.createNewFile();
				logger.debug("Unzipping file " + entry.getName() + " from archive " + source.getName() + " to " + tempFile.getAbsolutePath());
				BufferedOutputStream out = new BufferedOutputStream(new FileOutputStream(tempFile));

				int size;
				byte[] buffer = new byte[2048];
				while ((size = in.read(buffer, 0, buffer.length)) != -1) {
					out.write(buffer, 0, size);
				}
				// for (int c = in.read(); c != -1; c = in.read()) {
				// out.write(c);
				// }
				if (entry != null)
					in.closeEntry();
				if (out != null) {
					out.flush();
					out.close();
				}
			}
		} catch (FileNotFoundException e) {
			logger.debug("Encountered FileNotFound Exception, probably due to trying to extract a directory. Ignoring");
		} catch (IOException e) {
			logger.error(e.toString(), e);
		} finally {
			if (in != null)
				in.close();
		}

		return fileList;
	}

	/**
	 * Splits a multiline String into an array of single lines
	 * 
	 * @param string
	 * @param separator
	 *            String separating the lines, if ==null, lineSeparator will be used,
	 * @return
	 */
	public static ArrayList<String> splitIntoLines(String string, String separator) {
		String result = "";
		if (separator == null)
			separator = lineSeparator;

		String[] lineArray = string.split(separator);
		return new ArrayList<String>(Arrays.asList(lineArray));
	}

	/**
	 * Concats a list of Strings into a single String,
	 * 
	 * @param lines
	 * @param separator
	 *            String separating the lines, if ==null, lineSeparator will be used,
	 * @return
	 */
	public static String concatLines(List<String> lines, String separator) {
		if (separator == null)
			separator = lineSeparator;
		String result = "";

		for (String line : lines) {
			result.concat(line + separator);
		}

		return result.trim();
	}

	/**
	 * Returns a String containing a human readable representation of the current date, and the current time if that parameter is true
	 * 
	 * @param timeOfDay
	 * @return
	 */
	public static String getCurrentDateString(boolean timeOfDay) {
		Calendar cal = GregorianCalendar.getInstance();
		Date date = cal.getTime();

		SimpleDateFormat simpDate;
		if (timeOfDay) {
			simpDate = new SimpleDateFormat("dd.MM.yyyy HH:mm:ss z");
		} else {
			simpDate = new SimpleDateFormat("dd.MM.yyyy");
		}
		return simpDate.format(date);

		// if(timeOfDay)
		// dateFormat = DateFormat.getInstance();
		// else
		// dateFormat = DateFormat.getDateInstance();
		// return dateFormat.format(date);
	}

	/**
	 * Returns a String containing a human readable representation of the current time, including milliseconds if that parameter is true
	 * 
	 * @param millis
	 * @return
	 */
	public static String getCurrentTimeString(boolean millis) {
		DecimalFormat millisNumberFormat = new DecimalFormat("000");
		Calendar cal = GregorianCalendar.getInstance();
		Date date = cal.getTime();

		SimpleDateFormat simpDate;
		if (millis) {
			simpDate = new SimpleDateFormat("HH:mm:ss.SSS z");
		} else {
			simpDate = new SimpleDateFormat("HH:mm:ss z");
		}
		return simpDate.format(date);

		// DateFormat dateFormat = DateFormat.getTimeInstance();
		// if (millis) {
		// long ms = date.getTime() % 1000;
		// return dateFormat.format(date) + "." + millisNumberFormat.format(ms);
		// } else {
		// return dateFormat.format(date);
		// }
	}

	public static FilenameFilter ZipFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			if (name.endsWith("zip") || name.endsWith("ZIP")) {
				validImage = true;
			}
			return validImage;
		}
	};
	public static FilenameFilter PdfFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			if (name.endsWith("pdf") || name.endsWith("PDF")) {
				validImage = true;
			}
			return validImage;
		}
	};
	public static FilenameFilter XmlFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			// jpeg
			if (name.endsWith("xml") || name.endsWith("xml")) {
				validImage = true;
			}
			return validImage;
		}
	};
	public static FilenameFilter ImageFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			// jpeg
			if (name.endsWith("jpg") || name.endsWith("JPG") || name.endsWith("jpeg") || name.endsWith("JPEG")) {
				validImage = true;
			}
			if (name.endsWith(".tif") || name.endsWith(".TIF")) {
				validImage = true;
			}
			// png
			if (name.endsWith(".png") || name.endsWith(".PNG")) {
				validImage = true;
			}
			// gif
			if (name.endsWith(".gif") || name.endsWith(".GIF")) {
				validImage = true;
			}
			// jpeg2000
			if (name.endsWith(".jp2") || name.endsWith(".JP2")) {
				validImage = true;
			}

			return validImage;
		}
	};

	// Filters for file searches
	public static FileFilter DirFilter = new FileFilter() {
		public boolean accept(File file) {
			return file.isDirectory();
		}
	};

}
